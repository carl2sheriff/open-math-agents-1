import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2

-- Reduction WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2.R1 of WOWII Conjecture 189
-- Credit: @carl2sheriff
-- Copied lemmas (h11, sigma_ge, lemma4x, longer_of_perm_x, no_insert_x, lemma5abx,
-- exists_longest_x0, chain_rev, rot_head, h18) come from reduction R2.H1, themselves adapted
-- from reduction R1 by @computerfreak97 (PR #2971), itself adapting philipsaint's Dirac formalization.

/-
Table lemme -> lot (blueprint-D) ; balises `-- <<Bn>>` ... `-- <</Bn>>` (un lemme par balise,
`<<Bn.nom>>` quand Bn en contient plusieurs). Auxiliaires du lot : prefixe `bn_`, a placer
entre les balises du lemme concerne. Le texte hors balises est fige (copie H1 + main).
 Lot 1 : B1 (hmax_sup, reverse, getD_reverse, exists_cadre), B2 (deg_x0_le), B3 (card_le_gamma),
         B4 (cut_closed), B5 (no_longer, no_mid, no_pre, no_suf), B6 (endE, endE_last)
 Lot 2 : B7 (ring_card, T_lt, prog), B8 (J_bounds, dset_dist, degree_split), B9 (count_Q2),
         B10 (no_edge_comp), B11 (Rdeg2), B12 (m_ge), B13 (two_attach),
         B14 (R_ge3, R_card, R3, R4)
 Lot 3 : B15 (small_sigma), B16 (pack), B17 (hole_x0), B18 (x0_attach), B19 (walk_x0),
         B20 (head_deg_le, head_forced, last_deg_le, last_forced)
 Lot 4 : B21 (K3), B22 (C1, C3, C4, C5, C9, C10)
 Lot 5 : B23 (R4_nonclique), B24 (R4_clique, C11), B25 (thm_D_all) ; `main` (B26) est prouve.
Pas de `Cadre` : hypotheses explicites dans chaque lemme (voir le bloc de binders de `Cadre.hmax_sup`).
Jset/Dset/Rset du blueprint sont ecrits en ligne (filter/image) dans les enonces.
Deviation : head_forced / last_forced ont une hypothese en plus (hCr : C dans les indices valides).
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1

section Hyps
open SimpleGraph

/-- 2-connected case, `2σ + 7 ≤ n`, minimum degree equal to `σ`. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 7 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    G.minDegree = secondSmallestDegree G →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- 2-connected case, `2σ + 7 ≤ n`, minimum degree below `σ`. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 7 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    G.minDegree < secondSmallestDegree G →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

end Hyps

section Aux
open SimpleGraph OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- H1.1: minimum degree at least 2. -/
lemma h11 [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V) : ∀ v, 2 ≤ G.degree v := by
  classical
  intro v
  by_contra hlt
  push Not at hlt
  have hpos : 0 < G.degree v := by
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p⟩ := hconn.preconnected v w
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ =>
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨_, (mem_neighborFinset _ _ _).mpr h⟩
  have h1 : G.degree v = 1 := by omega
  obtain ⟨c', hc', huniq⟩ := (G.degree_eq_one_iff_existsUnique_adj).mp h1
  have hdist : ∀ w, w ≠ v → G.dist v w = 1 + G.dist c' w := by
    intro w hw
    apply le_antisymm
    · have := hconn.dist_triangle (u := v) (v := c') (w := w)
      have h2 : G.dist v c' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hc'
      omega
    · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v w
      cases p with
      | nil => exact absurd rfl hw
      | @cons _ z _ h q =>
        have hz : z = c' := huniq z h
        subst hz
        have := SimpleGraph.dist_le q
        simp only [Walk.length_cons] at hp
        omega
  have key : ∀ w, Even (G.dist c' w) ↔ ¬ Even (G.dist v w) := by
    intro w
    by_cases hw : w = v
    · subst hw
      have : G.dist c' w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hc'.symm
      simp [this]
    · rw [hdist w hw, Nat.even_iff, Nat.even_iff]
      omega
  have hsum : distEven G v + distEven G c' = Fintype.card V := by
    unfold distEven
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun w => Even (G.dist v w))
    simp only [key] at *
    rw [Finset.card_univ] at this
    simpa [key] using this
  have := hH v
  have := hH c'
  omega

/-- sigma at least 2 once minimum degree is at least 2. -/
lemma sigma_ge [Nontrivial V] [DecidableRel G.Adj] (h : ∀ v, 2 ≤ G.degree v) :
    2 ≤ secondSmallestDegree G := by
  have hlen : 1 < (degreeSequence G).length := by
    simp only [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hmem : secondSmallestDegree G ∈ degreeSequence G := by
    unfold secondSmallestDegree
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  simp only [degreeSequence, Multiset.mem_sort, Multiset.mem_map] at hmem
  obtain ⟨v, -, hv⟩ := hmem
  rw [← hv]; exact h v

/-- Lemma 4 for lists maximal among supersets of l. -/
lemma lemma4x [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
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
      (fun v hv => List.mem_cons_of_mem _ hv)
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
    have := hmax _ hnd hch (fun v hv => List.mem_append_left _ hv)
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
      have := hmax _ hnd' hch' (fun v hv => List.mem_cons_of_mem _
        ((hc'p.trans hperm).mem_iff.mpr hv))
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

/-- x -/
lemma longer_of_perm_x (l : List V) (hnd : l.Nodup)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) {c : List V} (hc : c.Perm (y :: l)) (hch : c.IsChain G.Adj) : False := by
  have hnd' : c.Nodup := hc.nodup_iff.mpr (List.nodup_cons.2 ⟨hy, hnd⟩)
  have := hmax c hnd' hch (fun v hv => hc.mem_iff.mpr (List.mem_cons_of_mem _ hv))
  rw [hc.length_eq] at this
  simp only [List.length_cons] at this
  omega

/-- Inserting an off-path vertex between two consecutive path vertices. -/
lemma no_insert_x (l : List V) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (k : ℕ) (hk0 : 0 < k) (hk : k < l.length)
    (h1 : G.Adj (l[k - 1]'(by omega)) y) (h2 : G.Adj y (l[k]'hk)) : False := by
  refine longer_of_perm_x l hnd hmax y hy (c := l.take k ++ y :: l.drop k)
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
lemma lemma5abx [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
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
    refine longer_of_perm_x l hnd hmax y hy (c := y :: l) (List.Perm.refl _) ?_
    refine List.IsChain.cons_of_ne_nil hne hch ?_
    rw [hhead]
    exact hadj
  have h1 : j + 1 < l.length := by
    by_contra h
    have hjl : j = l.length - 1 := by omega
    subst hjl
    refine longer_of_perm_x l hnd hmax y hy (c := l ++ [y]) (List.perm_append_comm.trans (List.Perm.refl _)) ?_
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
    exact no_insert_x l hnd hch hmax y hy (j + 1) (by omega) h1 (by simpa using hadj.symm) hadj2
  · rw [List.getD_eq_getElem _ _ (by omega : j - 1 < l.length)]
    intro hadj2
    exact no_insert_x l hnd hch hmax y hy j h0 hj hadj2.symm hadj
  · rw [List.getD_eq_getElem _ _ h1, hhead]
    intro hadj2
    refine longer_of_perm_x l hnd hmax y hy
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
    refine longer_of_perm_x l hnd hmax y hy
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


/-- Longest list among those containing `x₀`. -/
lemma exists_longest_x0 [DecidableRel G.Adj] (x₀ : V) :
    ∃ l : List V, l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l ∧
      ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length := by
  classical
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l) ∧ l.length = k
  have h1 : PP 1 := ⟨[x₀], ⟨by simp, List.isChain_singleton _, by simp⟩, rfl⟩
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨x₀⟩
  obtain ⟨l, ⟨hlnd, hlch, hlx⟩, hlM⟩ := Nat.findGreatest_spec (P := PP) hpos h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' →
      l'.length ≤ Nat.findGreatest PP (Fintype.card V) :=
    fun l' a b c => Nat.le_findGreatest a.length_le_card ⟨l', ⟨a, b, c⟩, rfl⟩
  exact ⟨l, List.ne_nil_of_mem hlx, hlnd, hlch, hlx, fun l' a b c => hlM ▸ hmax l' a b c⟩

lemma chain_rev {l : List V} (h : l.IsChain G.Adj) : l.reverse.IsChain G.Adj := by
  rw [List.isChain_reverse]
  exact h.imp (fun a b h => h.symm)

/-- rotation when the head is `x₀`. -/
lemma rot_head [DecidableRel G.Adj] (x₀ : V) (hδ : ∀ v, 2 ≤ G.degree v) (l : List V)
    (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj) (hx : x₀ ∈ l)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hh : l.head hne = x₀) :
    ∃ l' : List V, ∃ h : l' ≠ [], l'.Nodup ∧ l'.IsChain G.Adj ∧ x₀ ∈ l' ∧
      l'.length = l.length ∧ l'.head h ≠ x₀ ∧ l'.getLast h ≠ x₀ := by
  classical
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
    have hax : a = x₀ := hh
    subst hax
    have hxt : a ∉ t := (List.nodup_cons.mp hnd).1
    have hnt : t.Nodup := (List.nodup_cons.mp hnd).2
    have hnbr : ∀ y, G.Adj a y → y ∈ t := by
      intro y hy
      by_contra hyt
      have hyl : y ∉ a :: t := by
        simp only [List.mem_cons, not_or]
        exact ⟨hy.ne.symm, hyt⟩
      have := hmax (y :: a :: t) (List.nodup_cons.2 ⟨hyl, hnd⟩)
        (List.IsChain.cons_of_ne_nil hne hch hy.symm) (by simp)
      simp only [List.length_cons] at this
      omega
    have hcard : 1 < (G.neighborFinset a).card := by
      rw [card_neighborFinset_eq_degree]; have := hδ a; omega
    cases t with
    | nil =>
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset a).card)
      simpa using hnbr y ((mem_neighborFinset _ _ _).mp hy)
    | cons u t' =>
      obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne hcard u
      have hwadj : G.Adj a w := (mem_neighborFinset _ _ _).mp hw
      have hwt : w ∈ u :: t' := hnbr w hwadj
      obtain ⟨A, B, hAB⟩ := List.append_of_mem hwt
      have hA : A ≠ [] := by
        rintro rfl
        simp only [List.nil_append, List.cons.injEq] at hAB
        exact hwu hAB.1.symm
      have hch' : (A ++ w :: B).IsChain G.Adj := by
        rw [← hAB]; exact (List.isChain_cons.mp hch).2
      rw [List.isChain_append] at hch'
      have hlink : ∀ y ∈ A.head?, G.Adj a y := by
        intro y hy
        have hAh : (u :: t').head? = A.head? := by
          rw [hAB]
          cases A with
          | nil => exact absurd rfl hA
          | cons a1 A' => rfl
        exact (List.isChain_cons.mp hch).1 y (by rw [hAh]; exact hy)
      have hperm : (A.reverse ++ a :: w :: B).Perm (a :: u :: t') := by
        rw [List.perm_iff_count]
        intro z
        have h2 : (u :: t') = A ++ w :: B := hAB
        rw [h2]
        simp [List.count_cons, List.count_append]
        omega
      have hnd' : (A.reverse ++ a :: w :: B).Nodup := hperm.nodup_iff.mpr hnd
      refine ⟨A.reverse ++ a :: w :: B, by simp, hnd', ?_, by simp, hperm.length_eq, ?_, ?_⟩
      · rw [List.isChain_append]
        refine ⟨chain_rev hch'.1, ?_, ?_⟩
        · exact List.isChain_cons.mpr ⟨fun y hy => by
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            subst hy; exact hwadj, hch'.2.1⟩
        · intro x hx y hy
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          rw [List.getLast?_reverse] at hx
          exact (hlink x hx).symm
      · have hxA : a ∉ A := fun h => hxt (by rw [hAB]; exact List.mem_append_left _ h)
        intro hh2
        have hmem : (A.reverse ++ a :: w :: B).head (by simp) ∈ A.reverse := by
          rw [List.head_append_of_ne_nil (by simpa using hA)]
          exact List.head_mem _
        rw [hh2] at hmem
        exact hxA (List.mem_reverse.mp hmem)
      · intro hh2
        have hg := List.getLast_eq_getElem (l := A.reverse ++ a :: w :: B) (by simp)
        have hi : (A.reverse ++ a :: w :: B)[A.reverse.length]'(by simp) = a := by
          rw [List.getElem_append_right (by omega)]; simp
        have hinj := (List.Nodup.getElem_inj_iff hnd').mp (hi.trans (hh2.symm.trans hg))
        simp at hinj

/-- H1.8: ends different from `x₀`. -/
lemma h18 [DecidableRel G.Adj] (hconn : G.Connected) (x₀ : V) (hδ : ∀ v, 2 ≤ G.degree v)
    (hlt : ∀ l : List V, l.Nodup → l.IsChain G.Adj → x₀ ∈ l → l.length < Fintype.card V) :
    ∃ l : List V, ∃ h : l ≠ [], l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l ∧
      l.head h ≠ x₀ ∧ l.getLast h ≠ x₀ ∧
      (∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length) := by
  obtain ⟨l, hne, hnd, hch, hx, hmax⟩ := exists_longest_x0 (G := G) x₀
  by_cases h1 : l.head hne = x₀
  · obtain ⟨l', h', hnd', hch', hx', hlen, h2, h3⟩ :=
      rot_head x₀ hδ l hne hnd hch hx hmax h1
    exact ⟨l', h', hnd', hch', hx', h2, h3, fun l'' a b c => (hmax l'' a b c).trans hlen.ge⟩
  by_cases h2 : l.getLast hne = x₀
  · have hrne : l.reverse ≠ [] := by simpa using hne
    have hhead : l.reverse.head hrne = x₀ := by
      rw [List.head_reverse]; exact h2
    have hmaxr : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' →
        l'.length ≤ l.reverse.length := by
      intro l' a b c; rw [List.length_reverse]; exact hmax l' a b c
    obtain ⟨l', h', hnd', hch', hx', hlen, h3, h4⟩ :=
      rot_head x₀ hδ l.reverse hrne (List.nodup_reverse.mpr hnd) (chain_rev hch)
        (List.mem_reverse.mpr hx) hmaxr hhead
    exact ⟨l', h', hnd', hch', hx', h3, h4, fun l'' a b c => (hmaxr l'' a b c).trans hlen.ge⟩
  · exact ⟨l, hne, hnd, hch, hx, h1, h2, hmax⟩

-- <<B1.hmax_sup>>
lemma Cadre.hmax_sup [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length := by
  intro l' h1 h2 h3
  exact hmax l' h1 h2 (h3 x₀ hmem)
-- <</B1.hmax_sup>>

-- <<B1.reverse>>
lemma Cadre.reverse [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ∃ hne' : l.reverse ≠ [], l.reverse.Nodup ∧ l.reverse.IsChain G.Adj ∧ x₀ ∈ l.reverse ∧
      l.reverse.head hne' ≠ x₀ ∧ l.reverse.getLast hne' ≠ x₀ ∧
      (∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.reverse.length) ∧
      l.reverse.length < Fintype.card V := by
  have hne' : l.reverse ≠ [] := by simpa using hne
  refine ⟨hne', List.nodup_reverse.mpr hnd, chain_rev hch, List.mem_reverse.mpr hmem, ?_, ?_, ?_, ?_⟩
  · rw [List.head_reverse]; exact hlast
  · rw [List.getLast_reverse]; exact hhd
  · intro l' a b c; rw [List.length_reverse]; exact hmax l' a b c
  · rw [List.length_reverse]; exact hlt
-- <</B1.reverse>>

-- <<B1.getD_reverse>>
lemma Cadre.getD_reverse (l : List V) (d : V) {i : ℕ} (hi : i < l.length) :
    l.reverse.getD i d = l.getD (l.length - 1 - i) d := by
  have h1 : l.length - 1 - i < l.length := by omega
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ h1,
    List.getElem_reverse]
-- <</B1.getD_reverse>>

-- <<B1.exists_cadre>>
lemma Cadre.exists_cadre [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V) {x₀ : V}
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v) :
    (∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) ∨
      ∃ l : List V, ∃ hne : l ≠ [], l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l ∧
        l.head hne ≠ x₀ ∧ l.getLast hne ≠ x₀ ∧
        (∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length) ∧
        l.length < Fintype.card V := by
  classical
  have hδ := h11 hconn hH hn
  by_cases hall : ∀ l : List V, l.Nodup → l.IsChain G.Adj → x₀ ∈ l → l.length < Fintype.card V
  · right
    obtain ⟨l, hne, hnd, hch, hx, h1h, hlast, hmax⟩ := h18 hconn x₀ hδ hall
    exact ⟨l, hne, hnd, hch, hx, h1h, hlast, hmax, hall l hnd hch hx⟩
  · left
    push Not at hall
    obtain ⟨l, hnd, hch, hx, hlen⟩ := hall
    have hne : l ≠ [] := List.ne_nil_of_mem hx
    exact ham_of_list l hne hnd hch (le_antisymm hnd.length_le_card hlen)
-- <</B1.exists_cadre>>

-- <<B2>>
lemma deg_x0_le [Nontrivial V] [DecidableRel G.Adj] {x₀ : V}
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v) : G.degree x₀ ≤ secondSmallestDegree G := by
  have hlen : 1 < (degreeSequence G).length := by
    simp only [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hmem : secondSmallestDegree G ∈ degreeSequence G := by
    unfold secondSmallestDegree
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  simp only [degreeSequence, Multiset.mem_sort, Multiset.mem_map] at hmem
  obtain ⟨v, -, hv⟩ := hmem
  rw [← hv]; exact hmin v
-- <</B2>>

-- <<B3>>
lemma card_le_gamma [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) (v : V) (S : Finset V)
    (hS : ∀ w ∈ S, G.dist v w = 2) : S.card ≤ secondSmallestDegree G := by
  classical
  have hsub : S ⊆ (Finset.univ.filter fun w => Even (G.dist v w)).erase v := by
    intro w hw
    have h2 := hS w hw
    have hwv : w ≠ v := by
      rintro rfl
      simp at h2
    simp [hwv, h2]
  have hvm : v ∈ Finset.univ.filter fun w => Even (G.dist v w) := by simp
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hvm] at this
  have h3 := hH v
  unfold distEven at h3
  omega
-- <</B3>>

-- <<B4>>
lemma cut_closed (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected) (c : V) (S : Finset V)
    (hc : c ∉ S) (hS : S.Nonempty) (hcl : ∀ v ∈ S, ∀ w, G.Adj v w → w ≠ c → w ∈ S)
    (hout : ∃ w, w ≠ c ∧ w ∉ S) : False := by
  classical
  obtain ⟨s, hs⟩ := hS
  obtain ⟨w, hwc, hwS⟩ := hout
  have hsc : s ≠ c := fun h => hc (h ▸ hs)
  obtain ⟨p⟩ := (hb c) ⟨s, hsc⟩ ⟨w, hwc⟩
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x.1 ∈ S} hs hwS
  exact hd2 (hcl _ hd1 _ d.adj d.snd.2)
-- <</B4>>

-- <<B5.no_longer>>
lemma Cadre.no_longer [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (l' : List V) (h1 : l'.Nodup) (h2 : l'.IsChain G.Adj) (h3 : x₀ ∈ l')
    (h4 : l.length < l'.length) : False := by
  have := hmax l' h1 h2 h3
  omega
-- <</B5.no_longer>>

-- <<B5.no_mid>>
lemma b5_chain3 {A B C : List V} (hB : B ≠ []) (hA : A.IsChain G.Adj) (hb : B.IsChain G.Adj)
    (hc : C.IsChain G.Adj) (hAB : ∀ x ∈ A.getLast?, ∀ y ∈ B.head?, G.Adj x y)
    (hBC : ∀ x ∈ B.getLast?, ∀ y ∈ C.head?, G.Adj x y) : (A ++ B ++ C).IsChain G.Adj := by
  rw [List.isChain_append]
  refine ⟨List.isChain_append.2 ⟨hA, hb, hAB⟩, hc, ?_⟩
  intro x hx y hy
  rw [List.getLast?_append_of_ne_nil _ hB] at hx
  exact hBC x hx y hy

lemma b5_idx {l : List V} {x : V} (h : x ∈ l) : ∃ i, i < l.length ∧ l.getD i x = x := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩

lemma b5_mem_td {l : List V} {x : V} {A B i : ℕ} (hi : i < l.length) (h : l.getD i x = x)
    (hc : i < A ∨ B ≤ i) : x ∈ l.take A ∨ x ∈ l.drop B := by
  rw [List.getD_eq_getElem _ _ hi] at h
  rcases hc with hc | hc
  · left
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simpa using h⟩
  · right
    refine List.mem_iff_getElem.mpr ⟨i - B, by simp; omega, ?_⟩
    rw [List.getElem_drop]
    have : B + (i - B) = i := by omega
    simpa [this] using h

lemma b5_head_drop {l : List V} {b : ℕ} (d : V) (hb : b < l.length) :
    (l.drop b).head? = some (l.getD b d) := by
  rw [List.head?_drop, List.getD_eq_getElem _ _ hb, List.getElem?_eq_getElem hb]

lemma b5_last_take {l : List V} {a : ℕ} (d : V) (ha : a < l.length) :
    (l.take (a + 1)).getLast? = some (l.getD a d) := by
  rw [List.getLast?_take, List.getD_eq_getElem _ _ ha]
  simp [List.getElem?_eq_getElem ha]

lemma b5_nodup_td {l : List V} (hnd : l.Nodup) {A B : ℕ} (hAB : A ≤ B) :
    (l.take A ++ l.drop B).Nodup := by
  have hsub : (l.take A ++ l.drop B).Sublist l := by
    have h1 : l.drop B = (l.drop A).drop (B - A) := by
      rw [List.drop_drop]; congr 1; omega
    have h2 : (l.take A ++ (l.drop A).drop (B - A)).Sublist (l.take A ++ l.drop A) :=
      List.Sublist.append (List.Sublist.refl _) (List.drop_sublist _ _)
    rw [h1]
    simpa using h2
  exact hsub.nodup hnd

lemma Cadre.no_mid [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (a b : ℕ) (hab : a < b) (hb' : b < l.length)
    (h1 : G.Adj (l.getD a x₀) (s.head hs)) (h2 : G.Adj (s.getLast hs) (l.getD b x₀))
    (hx : ∀ i, a < i → i < b → l.getD i x₀ ≠ x₀) (hlen : b - a - 1 < s.length) : False := by
  have hT : (l.take (a + 1)).length = a + 1 := by simp; omega
  have hD : (l.drop b).length = l.length - b := by simp
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (l.take (a + 1) ++ s ++ l.drop b) ?_ ?_ ?_ ?_
  · have hTD := b5_nodup_td hnd (A := a + 1) (B := b) (by omega)
    rw [List.nodup_append]
    refine ⟨List.nodup_append.2 ⟨hnd.sublist (List.take_sublist _ _), snd, ?_⟩,
      hnd.sublist (List.drop_sublist _ _), ?_⟩
    · intro x hx y hy hxy
      exact sl y hy (hxy ▸ List.take_subset _ _ hx)
    · intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact (List.nodup_append.1 hTD).2.2 x hx y hy
      · rintro rfl
        exact sl x hx (List.drop_subset _ _ hy)
  · refine b5_chain3 hs (hch.take _) sch (hch.drop _) ?_ ?_
    · intro x hx y hy
      rw [b5_last_take x₀ (by omega)] at hx
      rw [List.head?_eq_head hs] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h1
    · intro x hx y hy
      rw [b5_head_drop x₀ hb'] at hy
      rw [List.getLast?_eq_getLast hs] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h2
  · obtain ⟨i, hi, hxi⟩ := b5_idx hmem
    have hc : i < a + 1 ∨ b ≤ i := by
      by_contra hcon
      push Not at hcon
      exact hx i (by omega) hcon.2 (by rw [hxi])
    rcases b5_mem_td hi hxi hc with h | h
    · simp [h]
    · simp [h]
  · simp only [List.length_append, hT, hD]
    omega
-- <</B5.no_mid>>

-- <<B5.no_pre>>
lemma Cadre.no_pre [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (a : ℕ) (ha : a < l.length) (h : G.Adj (s.getLast hs) (l.getD a x₀))
    (hx : ∀ i, i < a → l.getD i x₀ ≠ x₀) (hlen : a < s.length) : False := by
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (s ++ l.drop a) ?_ ?_ ?_ ?_
  · refine List.nodup_append.2 ⟨snd, hnd.sublist (List.drop_sublist _ _), ?_⟩
    intro x hx y hy hxy
    exact sl x hx (hxy ▸ List.drop_subset _ _ hy)
  · refine List.isChain_append.2 ⟨sch, hch.drop _, ?_⟩
    intro x hx y hy
    rw [b5_head_drop x₀ ha] at hy
    rw [List.getLast?_eq_getLast hs] at hx
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx; subst hy; exact h
  · obtain ⟨i, hi, hxi⟩ := b5_idx hmem
    have hc : i < 0 ∨ a ≤ i := by
      by_contra hcon
      push Not at hcon
      exact hx i (by omega) (by rw [hxi])
    rcases b5_mem_td (A := 0) (B := a) hi hxi hc with h | h
    · simp at h
    · simp [h]
  · simp only [List.length_append, List.length_drop]
    omega
-- <</B5.no_pre>>

-- <<B5.no_suf>>
lemma Cadre.no_suf [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (b : ℕ) (hb' : b < l.length) (h : G.Adj (l.getD b x₀) (s.head hs))
    (hx : ∀ i, b < i → i < l.length → l.getD i x₀ ≠ x₀) (hlen : l.length - 1 - b < s.length) :
    False := by
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (l.take (b + 1) ++ s) ?_ ?_ ?_ ?_
  · refine List.nodup_append.2 ⟨hnd.sublist (List.take_sublist _ _), snd, ?_⟩
    intro x hx y hy hxy
    exact sl y hy (hxy ▸ List.take_subset _ _ hx)
  · refine List.isChain_append.2 ⟨hch.take _, sch, ?_⟩
    intro x hx y hy
    rw [b5_last_take x₀ hb'] at hx
    rw [List.head?_eq_head hs] at hy
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx; subst hy; exact h
  · obtain ⟨i, hi, hxi⟩ := b5_idx hmem
    have hc : i < b + 1 ∨ l.length ≤ i := by
      by_contra hcon
      push Not at hcon
      exact hx i (by omega) hi (by rw [hxi])
    rcases b5_mem_td (A := b + 1) (B := l.length) hi hxi hc with h | h
    · simp [h]
    · simp at h
  · simp only [List.length_append, List.length_take]
    omega
-- <</B5.no_suf>>

-- <<B6.endE>>
lemma Cadre.endE [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (a j : ℕ) (haj : a < j) (hj : j < l.length)
    (h1 : G.Adj (l.getD 0 x₀) (l.getD j x₀)) (h2 : G.Adj (s.getLast hs) (l.getD a x₀))
    (hx : ∃ i, (i ≤ a ∨ j ≤ i) ∧ i < l.length ∧ l.getD i x₀ = x₀) (hlen : j - a ≤ s.length) :
    False := by
  have hT : (l.take (a + 1)).length = a + 1 := by simp; omega
  have hhead : (l.take (a + 1)).head? = some (l.getD 0 x₀) := by
    rw [List.head?_take, if_neg (by omega), List.head?_eq_getElem?,
      List.getD_eq_getElem _ _ (by omega), List.getElem?_eq_getElem (by omega)]
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (s ++ (l.take (a + 1)).reverse ++ l.drop j) ?_ ?_ ?_ ?_
  · have hTD := b5_nodup_td hnd (A := a + 1) (B := j) (by omega)
    have hTn : (l.take (a + 1)).reverse.Nodup :=
      List.nodup_reverse.mpr (hnd.sublist (List.take_sublist _ _))
    rw [List.nodup_append]
    refine ⟨List.nodup_append.2 ⟨snd, hTn, ?_⟩, hnd.sublist (List.drop_sublist _ _), ?_⟩
    · intro x hx y hy hxy
      exact sl x hx (hxy ▸ List.take_subset _ _ (List.mem_reverse.mp hy))
    · intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · rintro rfl
        exact sl x hx (List.drop_subset _ _ hy)
      · exact (List.nodup_append.1 hTD).2.2 x (List.mem_reverse.mp hx) y hy
  · refine b5_chain3 (by rw [← List.length_pos_iff, List.length_reverse, hT]; omega) sch (chain_rev (hch.take _)) (hch.drop _) ?_ ?_
    · intro x hx y hy
      rw [List.head?_reverse, b5_last_take x₀ (by omega)] at hy
      rw [List.getLast?_eq_getLast hs] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h2
    · intro x hx y hy
      rw [List.getLast?_reverse, hhead] at hx
      rw [b5_head_drop x₀ hj] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h1
  · obtain ⟨i, hi, hxi, hc⟩ : ∃ i, i < l.length ∧ l.getD i x₀ = x₀ ∧ (i < a + 1 ∨ j ≤ i) := by
      obtain ⟨i, hc, hi, he⟩ := hx
      exact ⟨i, hi, he, by omega⟩
    rcases b5_mem_td hi hxi hc with h | h
    · simp [h]
    · simp [h]
  · simp only [List.length_append, List.length_reverse, hT, List.length_drop]
    omega
-- <</B6.endE>>

-- <<B6.endE_last>>
lemma Cadre.endE_last [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (a j : ℕ) (hja : j < a) (ha : a < l.length)
    (h1 : G.Adj (l.getD (l.length - 1) x₀) (l.getD j x₀)) (h2 : G.Adj (s.head hs) (l.getD a x₀))
    (hx : ∃ i, (a ≤ i ∨ i ≤ j) ∧ i < l.length ∧ l.getD i x₀ = x₀) (hlen : a - j ≤ s.length) :
    False := by
  have hT : (l.drop a).length = l.length - a := by simp
  have hlast' : (l.drop a).getLast? = some (l.getD (l.length - 1) x₀) := by
    rw [List.getLast?_drop, if_neg (by omega), getD_last l hne, List.getLast?_eq_getLast hne]
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (l.take (j + 1) ++ (l.drop a).reverse ++ s) ?_ ?_ ?_ ?_
  · have hTD := b5_nodup_td hnd (A := j + 1) (B := a) (by omega)
    have hTn : (l.drop a).reverse.Nodup :=
      List.nodup_reverse.mpr (hnd.sublist (List.drop_sublist _ _))
    rw [List.nodup_append]
    refine ⟨List.nodup_append.2 ⟨hnd.sublist (List.take_sublist _ _), hTn, ?_⟩, snd, ?_⟩
    · intro x hx y hy
      exact (List.nodup_append.1 hTD).2.2 x hx y (List.mem_reverse.mp hy)
    · intro x hx y hy hxy
      rcases List.mem_append.mp hx with hx | hx
      · exact sl y hy (hxy ▸ List.take_subset _ _ hx)
      · exact sl y hy (hxy ▸ List.drop_subset _ _ (List.mem_reverse.mp hx))
  · refine b5_chain3 (by rw [← List.length_pos_iff, List.length_reverse, hT]; omega) (hch.take _) (chain_rev (hch.drop _)) sch ?_ ?_
    · intro x hx y hy
      rw [b5_last_take x₀ (by omega)] at hx
      rw [List.head?_reverse, hlast'] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h1.symm
    · intro x hx y hy
      rw [List.getLast?_reverse, b5_head_drop x₀ ha] at hx
      rw [List.head?_eq_head hs] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h2.symm
  · obtain ⟨i, hi, hxi, hc⟩ : ∃ i, i < l.length ∧ l.getD i x₀ = x₀ ∧ (i < j + 1 ∨ a ≤ i) := by
      obtain ⟨i, hc, hi, he⟩ := hx
      exact ⟨i, hi, he, by omega⟩
    rcases b5_mem_td hi hxi hc with h | h
    · simp [h]
    · simp [List.mem_reverse, h]
  · simp only [List.length_append, List.length_reverse, hT, List.length_take]
    omega
-- <</B6.endE_last>>

-- <<B7.ring_card>>
lemma ring_card (J : Finset ℕ) (h0 : 0 ∉ J) :
    (J.image (· + 1) ∪ J.image (· - 1)).card + (J.filter (fun j => j + 2 ∈ J)).card =
      2 * J.card := by
  have h1 : (J.image (· + 1)).card = J.card :=
    Finset.card_image_of_injective _ (add_left_injective 1)
  have h2 : (J.image (· - 1)).card = J.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
    have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
    simp only at hab
    omega
  have h3 : J.image (· + 1) ∩ J.image (· - 1) = (J.filter (fun j => j + 2 ∈ J)).image (· + 1) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hbx⟩⟩
      have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      have : b = a + 2 := by omega
      rw [← this]; exact hb
    · rintro ⟨a, ⟨ha, ha2⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨a + 2, ha2, by simp⟩⟩
  have h4 : ((J.filter (fun j => j + 2 ∈ J)).image (· + 1)).card = (J.filter (fun j => j + 2 ∈ J)).card :=
    Finset.card_image_of_injective _ (add_left_injective 1)
  have h5 := Finset.card_union_add_card_inter (J.image (· + 1)) (J.image (· - 1))
  rw [h3, h4, h1, h2] at h5
  omega
-- <</B7.ring_card>>

-- <<B7.T_lt>>
lemma T_lt (J : Finset ℕ) (hJ : J.Nonempty) :
    (J.filter (fun j => j + 2 ∈ J)).card + 1 ≤ J.card := by
  have hsub : J.filter (fun j => j + 2 ∈ J) ⊆ J.erase (J.max' hJ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_erase]
    refine ⟨?_, hj.1⟩
    have := Finset.le_max' J _ hj.2
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.max'_mem J hJ)] at this
  have := Finset.card_pos.mpr hJ
  omega
-- <</B7.T_lt>>

-- <<B7.prog>>
lemma prog (J : Finset ℕ) (hJ : J.Nonempty)
    (ht : (J.filter (fun j => j + 2 ∈ J)).card + 1 = J.card) :
    (∀ j ∈ J, j ≠ J.max' hJ → j + 2 ∈ J) ∧ (∀ j ∈ J, j ≠ J.min' hJ → 2 ≤ j ∧ j - 2 ∈ J) := by
  have hsub : J.filter (fun j => j + 2 ∈ J) ⊆ J.erase (J.max' hJ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_erase]
    refine ⟨?_, hj.1⟩
    have := Finset.le_max' J _ hj.2
    omega
  have hc := Finset.card_erase_of_mem (Finset.max'_mem J hJ)
  have hpos := Finset.card_pos.mpr hJ
  have heq : J.filter (fun j => j + 2 ∈ J) = J.erase (J.max' hJ) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨?_, ?_⟩
  · intro j hj hne
    have : j ∈ J.erase (J.max' hJ) := Finset.mem_erase.mpr ⟨hne, hj⟩
    rw [← heq] at this
    exact (Finset.mem_filter.mp this).2
  · have hsub2 : (J.filter (fun j => j + 2 ∈ J)).image (· + 2) ⊆ J.erase (J.min' hJ) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨j, ⟨hj, hj2⟩, rfl⟩ := hx
      rw [Finset.mem_erase]
      refine ⟨?_, hj2⟩
      have := Finset.min'_le J _ hj
      omega
    have hc2 := Finset.card_erase_of_mem (Finset.min'_mem J hJ)
    have hci : ((J.filter (fun j => j + 2 ∈ J)).image (· + 2)).card = (J.filter (fun j => j + 2 ∈ J)).card :=
      Finset.card_image_of_injective _ (add_left_injective 2)
    have heq2 := Finset.eq_of_subset_of_card_le hsub2 (by omega)
    intro j hj hne
    have : j ∈ J.erase (J.min' hJ) := Finset.mem_erase.mpr ⟨hne, hj⟩
    rw [← heq2] at this
    simp only [Finset.mem_image, Finset.mem_filter] at this
    obtain ⟨i, ⟨hi, _⟩, rfl⟩ := this
    exact ⟨by omega, by simpa using hi⟩
-- <</B7.prog>>

-- <<B8.J_bounds>>
lemma Cadre.J_bounds [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    {y : V} (hy : y ∉ l) {j : ℕ} (hj : j ∈ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)))) : 0 < j ∧ j + 1 < l.length := by
  rw [Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨hjl, hadj⟩ := hj
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hgd : l.getD j y = l.getD j x₀ := by
    rw [List.getD_eq_getElem _ _ hjl, List.getD_eq_getElem _ _ hjl]
  have := lemma5abx hconn l hne hnd hch hhs y hy j hjl (by rw [hgd]; exact hadj)
  exact ⟨this.1, this.2.1⟩
-- <</B8.J_bounds>>

-- <<B8.dset_dist>>
lemma Cadre.dset_dist [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    {y : V} (hy : y ∉ l) {i : ℕ} (hi : i ∈ (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1))) :
    i < l.length ∧ G.dist y (l.getD i x₀) = 2 := by
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hi
  have key : ∀ j, j < l.length → G.Adj y (l.getD j x₀) →
      (j + 1 < l.length ∧ G.dist y (l.getD (j + 1) x₀) = 2) ∧
        (0 < j ∧ G.dist y (l.getD (j - 1) x₀) = 2) := by
    intro j hjl hadj
    have hgd : ∀ k, k < l.length → l.getD k y = l.getD k x₀ := by
      intro k hk; rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]
    have h5 := lemma5abx hconn l hne hnd hch hhs y hy j hjl (by rw [hgd j hjl]; exact hadj)
    obtain ⟨h0, h1, h2, h3, -, -⟩ := h5
    have hk1 : j + 1 < l.length := h1
    have hk2 : j - 1 < l.length := by omega
    rw [hgd _ hk1] at h2
    rw [hgd _ hk2] at h3
    have hch' : ∀ k, k + 1 < l.length → G.Adj (l.getD k x₀) (l.getD (k + 1) x₀) := by
      intro k hk
      have := List.isChain_iff_getElem.mp hch k hk
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk]
      exact this
    have hne1 : l.getD (j + 1) x₀ ≠ y := by
      intro h; apply hy; rw [← h, List.getD_eq_getElem _ _ hk1]; exact List.getElem_mem _
    have hne2 : l.getD (j - 1) x₀ ≠ y := by
      intro h; apply hy; rw [← h, List.getD_eq_getElem _ _ hk2]; exact List.getElem_mem _
    refine ⟨⟨hk1, dist_two hconn hadj (hch' j hk1) h2 hne1⟩, ⟨h0, ?_⟩⟩
    have hj1 : j - 1 + 1 = j := by omega
    have hc2 : G.Adj (l.getD j x₀) (l.getD (j - 1) x₀) := by
      have := hch' (j - 1) (by omega)
      rw [hj1] at this
      exact this.symm
    exact dist_two hconn hadj hc2 h3 hne2
  rcases hi with ⟨j, ⟨hjl, hadj⟩, rfl⟩ | ⟨j, ⟨hjl, hadj⟩, rfl⟩
  · exact ⟨(key j hjl hadj).1.1, (key j hjl hadj).1.2⟩
  · have := (key j hjl hadj).2
    exact ⟨by omega, this.2⟩
-- <</B8.dset_dist>>

-- <<B8.degree_split>>
lemma Cadre.degree_split [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    {y : V} (hy : y ∉ l) :
    G.degree y = (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)))).card + ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hdisj : Disjoint (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image
      (fun i => l.getD i x₀)) ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hw1 hw2
    obtain ⟨i, ⟨hi, _⟩, rfl⟩ := hw1
    apply hw2.1
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hN : G.neighborFinset y = ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image
      (fun i => l.getD i x₀) ∪ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · intro hw
      by_cases hwl : w ∈ l
      · left
        obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hwl
        refine ⟨i, ⟨hi, ?_⟩, ?_⟩
        · rw [List.getD_eq_getElem _ _ hi, hiw]; exact hw
        · rw [List.getD_eq_getElem _ _ hi, hiw]
      · right; exact ⟨hwl, hw⟩
    · rintro (⟨i, ⟨hi, hadj⟩, rfl⟩ | ⟨_, hw⟩)
      · exact hadj
      · exact hw
  rw [hN, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn]
  intro i hi j hj hij
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
  simp only at hij
  rw [List.getD_eq_getElem _ _ hi.1, List.getD_eq_getElem _ _ hj.1] at hij
  exact (List.Nodup.getElem_inj_iff hnd).mp hij
-- <</B8.degree_split>>

-- <<B9>>
lemma Cadre.count_Q2 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y : V) (hy : y ∉ l) (Bp K2 : Finset V)
    (hB : ∀ w ∈ Bp, w ∈ l ∧ ¬ G.Adj y w ∧ ∃ z, z ∉ l ∧ G.Adj y z ∧ G.Adj z w)
    (hK : ∀ w ∈ K2, w ∉ l ∧ w ≠ y ∧ ¬ G.Adj y w ∧ ∃ z, G.Adj y z ∧ G.Adj z w) :
    ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1))).card + Bp.card + K2.card ≤ secondSmallestDegree G := by
  classical
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hDd : ∀ i ∈ (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)),
      i < l.length ∧ G.dist y (l.getD i x₀) = 2 := fun i hi =>
    Cadre.dset_dist hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hi
  have hdisjDB : Disjoint ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)).image (fun i => l.getD i x₀)) Bp := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp hw1
    obtain ⟨-, -, z, hz, hyz, hzw⟩ := hB _ hw2
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hiD
    rcases hiD with ⟨j, ⟨hjl, hadj⟩, rfl⟩ | ⟨j, ⟨hjl, hadj⟩, rfl⟩
    · have hjb := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
        (j := j) (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hjl, hadj⟩)
      refine Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, z] (by simp) (by simp; exact G.ne_of_adj hyz) (by simp [hyz]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption) j (j + 1) (by omega) hjb.2 (by simpa using hadj.symm) (by simpa using hzw) (by intro i h1 h2; omega) (by simp)
    · have hjb := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
        (j := j) (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hjl, hadj⟩)
      refine Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [z, y] (by simp) (by simp; exact (G.ne_of_adj hyz).symm) (by simp [hyz.symm]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption) (j - 1) j (by omega) (by omega) (by simpa using hzw.symm) (by simpa using hadj) (by intro i h1 h2; omega) (by simp only [List.length_cons, List.length_nil]; omega)
  have hdisjK : Disjoint ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)).image (fun i => l.getD i x₀) ∪ Bp) K2 := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have hwl : w ∈ l := by
      rcases Finset.mem_union.mp hw1 with h | h
      · obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp h
        rw [List.getD_eq_getElem _ _ (hDd i hiD).1]; exact List.getElem_mem _
      · exact (hB w h).1
    exact (hK w hw2).1 hwl
  have hinj : Set.InjOn (fun i => l.getD i x₀) (((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)) : Finset ℕ) : Set ℕ) := by
    intro i hi j hj hij
    have hi' := (hDd i hi).1
    have hj' := (hDd j hj).1
    simp only at hij
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at hij
    exact (List.Nodup.getElem_inj_iff hnd).mp hij
  have hcard := card_le_gamma hconn hH y
    ((((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)).image (fun i => l.getD i x₀) ∪ Bp) ∪ K2)) (by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · rcases Finset.mem_union.mp h with h | h
        · obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp h
          exact (hDd i hiD).2
        · obtain ⟨hwl, hnadj, z, -, hyz, hzw⟩ := hB w h
          exact dist_two hconn hyz hzw hnadj (fun h => hy (h ▸ hwl))
      · obtain ⟨-, hwy, hnadj, z, hyz, hzw⟩ := hK w h
        exact dist_two hconn hyz hzw hnadj hwy)
  rw [Finset.card_union_of_disjoint hdisjK, Finset.card_union_of_disjoint hdisjDB,
    Finset.card_image_of_injOn hinj] at hcard
  exact hcard
-- <</B9>>

-- auxiliaires b15 (remontés pour B17)
lemma b15_adj {l : List V} (d : V) (hch : l.IsChain G.Adj) {i : ℕ} (hi : i + 1 < l.length) :
    G.Adj (l.getD i d) (l.getD (i + 1) d) := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  exact List.isChain_iff_getElem.1 hch i hi

lemma b15_inj {l : List V} (d : V) (hnd : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : l.getD i d = l.getD j d) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (List.Nodup.getElem_inj_iff hnd).1 h

lemma b15_mem {l : List V} (d : V) {i : ℕ} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

lemma b15_head {l : List V} (hne : l ≠ []) (d : V) : l.head hne = l.getD 0 d := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => rfl

lemma b15_last {l : List V} (hne : l ≠ []) (d : V) : l.getLast hne = l.getD (l.length - 1) d := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem _ _ (by have := List.length_pos_of_ne_nil hne; omega)]

lemma b15_dflt {l : List V} {i : ℕ} (hi : i < l.length) (d d' : V) : l.getD i d = l.getD i d' := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]

lemma b15_len2 {l : List V} {x₀ : V} (hne : l ≠ []) (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) :
    2 ≤ l.length := by
  by_contra hlt
  have h1 : l.length = 1 := by have := List.length_pos_of_ne_nil hne; omega
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 h1
  simp only [List.mem_singleton] at hmem
  exact hhd (by simp [hmem])


-- <<B17>>
lemma b17_decomp (l : List V) (d : V) {i : ℕ} (hi : i + 1 < l.length) :
    l = l.take i ++ l.getD i d :: l.getD (i + 1) d :: l.drop (i + 2) := by
  have h := List.take_append_drop i l
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)] at h
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  exact h.symm

lemma b17_long {x₀ : V} {l s c : List V} (hnd : l.Nodup) (sl : ∀ v ∈ s, v ∉ l)
    (snd : s.Nodup) (hs : s ≠ []) (hmem : x₀ ∈ l)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hc : c.Perm (s ++ l)) (hch : c.IsChain G.Adj) : False := by
  have hnd' : (s ++ l).Nodup :=
    List.nodup_append.2 ⟨snd, hnd, (fun a ha b hb h => sl a ha (h ▸ hb))⟩
  have h := hmax c (hc.nodup_iff.2 hnd') hch (hc.mem_iff.2 (List.mem_append_right _ hmem))
  rw [hc.length_eq, List.length_append] at h
  have := List.length_pos_of_ne_nil hs
  omega

lemma b17_perm1 (t d s : List V) (u x : V) :
    (t ++ x :: u :: (s ++ d)).Perm (s ++ (t ++ u :: x :: d)) := by
  refine List.perm_iff_count.2 (fun a => ?_)
  simp only [List.count_append, List.count_cons]
  split_ifs <;> omega

lemma b17_perm2 (t d s : List V) (w x : V) :
    (t ++ (s ++ w :: x :: d)).Perm (s ++ (t ++ x :: w :: d)) := by
  refine List.perm_iff_count.2 (fun a => ?_)
  simp only [List.count_append, List.count_cons]
  split_ifs <;> omega

lemma b17_head_app {s : List V} (hs : s ≠ []) (d : List V) : (s ++ d).head? = some (s.head hs) := by
  cases s with
  | nil => exact absurd rfl hs
  | cons a t => rfl

lemma b17_last_take {l : List V} (d : V) {p : ℕ} (hp : 1 ≤ p) (hpl : p ≤ l.length) :
    (l.take p).getLast? = some (l.getD (p - 1) d) := by
  rw [List.getLast?_take, if_neg (by omega), List.getD_eq_getElem _ _ (by omega)]
  simp [List.getElem?_eq_getElem (by omega : p - 1 < l.length)]

lemma b17_head_drop {l : List V} (d : V) {n : ℕ} (hn : n < l.length) :
    (l.drop n).head? = some (l.getD n d) := by
  rw [List.head?_drop, List.getD_eq_getElem _ _ hn, List.getElem?_eq_getElem hn]

lemma Cadre.hole_x0 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (S : Finset V) (hS : ∀ y ∈ S, y ∉ l) (p : ℕ) (hp : 1 ≤ p) (hp3 : p + 3 < l.length)
    (hx : l.getD (p + 1) x₀ = x₀)
    (hSA : ∀ y ∈ S, G.Adj y (l.getD p x₀) ∨ G.Adj y (l.getD (p + 2) x₀))
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l)
    (h1 : G.Adj (l.getD p x₀) (s.head hs)) (h2 : G.Adj (s.getLast hs) (l.getD (p + 2) x₀)) :
    S.card + 2 ≤ secondSmallestDegree G := by
  have hp2 : p + 2 < l.length := by omega
  have hA : G.Adj (l.getD p x₀) x₀ := by
    have := b15_adj (G := G) x₀ hch (i := p) (by omega)
    rwa [hx] at this
  have hB : G.Adj x₀ (l.getD (p + 2) x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p + 1) (by omega)
    rwa [hx] at this
  have hAa : G.Adj (l.getD (p - 1) x₀) (l.getD p x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p - 1) (by omega)
    rwa [Nat.sub_add_cancel hp] at this
  have hBb : G.Adj (l.getD (p + 2) x₀) (l.getD (p + 3) x₀) :=
    b15_adj (G := G) x₀ hch (i := p + 2) (by omega)
  have hsl := List.getLast?_eq_getLast hs
  have hna : ¬ G.Adj (l.getD (p - 1) x₀) x₀ := by
    intro hadj
    refine b17_long (l := l) (s := s) (c := l.take p ++ x₀ :: l.getD p x₀ :: (s ++ l.drop (p + 2)))
      hnd sl snd hs hmem hmax ?_ ?_
    · have hd := b17_decomp l x₀ (i := p) (by omega)
      rw [hx] at hd
      have := b17_perm1 (l.take p) (l.drop (p + 2)) s (l.getD p x₀) x₀
      rwa [← hd] at this
    · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
      · refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_, List.isChain_append.2 ⟨sch, hch.drop _, ?_⟩⟩⟩
        · intro z hz
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hA.symm
        · intro z hz
          rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact h1
        · intro z hz w hw
          rw [hsl, Option.mem_def, Option.some.injEq] at hz
          rw [b17_head_drop x₀ hp2, Option.mem_def, Option.some.injEq] at hw
          subst hz hw; exact h2
      · intro z hz w hw
        rw [b17_last_take x₀ hp (by omega), Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        subst hz hw; exact hadj
  have hnb : ¬ G.Adj x₀ (l.getD (p + 3) x₀) := by
    intro hadj
    refine b17_long (l := l) (s := s) (c := l.take (p + 1) ++ (s ++ l.getD (p + 2) x₀ :: x₀ :: l.drop (p + 3)))
      hnd sl snd hs hmem hmax ?_ ?_
    · have hd := b17_decomp l x₀ (i := p + 1) (by omega)
      rw [hx] at hd
      have := b17_perm2 (l.take (p + 1)) (l.drop (p + 1 + 2)) s (l.getD (p + 1 + 1) x₀) x₀
      rwa [← hd] at this
    · refine List.isChain_append.2 ⟨hch.take _, List.isChain_append.2 ⟨sch, ?_, ?_⟩, ?_⟩
      · refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_, hch.drop _⟩⟩
        · intro z hz
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hB.symm
        · intro z hz
          rw [b17_head_drop x₀ (by omega), Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hadj
      · intro z hz w hw
        rw [hsl, Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        subst hz hw; exact h2
      · intro z hz w hw
        rw [List.getLast?_take, if_neg (by omega)] at hz
        have hw' := hw
        rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hw'
        subst hw'
        simp only [List.getElem?_eq_getElem (by omega : p + 1 - 1 < l.length), Option.some_or,
          Option.mem_def, Option.some.injEq] at hz
        subst hz
        have e1 : l[p + 1 - 1]'(by omega) = l.getD p x₀ := by
          rw [List.getD_eq_getElem _ _ (by omega)]; simp
        rw [e1]; exact h1
  have hne_a : l.getD (p - 1) x₀ ≠ x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
    omega
  have hne_b : l.getD (p + 3) x₀ ≠ x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
    omega
  have hab : l.getD (p - 1) x₀ ≠ l.getD (p + 3) x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) h
    omega
  have hSd : ∀ y ∈ S, G.dist x₀ y = 2 := by
    intro y hy
    have hyl := hS y hy
    have hyx : y ≠ x₀ := fun h => hyl (h ▸ hmem)
    have hmx := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have key : ¬ G.Adj y x₀ := by
      intro hadj
      have hadj' : G.Adj y (l.getD (p + 1) y) := by
        rw [b15_dflt (l := l) (i := p + 1) (by omega) y x₀, hx]; exact hadj
      obtain ⟨-, -, h5, h6, -, -⟩ := lemma5abx hconn l hne hnd hch hmx y hyl (p + 1) (by omega) hadj'
      rw [Nat.add_sub_cancel] at h6
      rcases hSA y hy with h | h
      · exact h6 (by rwa [b15_dflt (l := l) (i := p) (by omega) y x₀])
      · exact h5 (by rwa [b15_dflt (l := l) (i := p + 1 + 1) (by omega) y x₀])
    rcases hSA y hy with h | h
    · exact dist_two hconn hA.symm h.symm (fun h' => key h'.symm) hyx
    · exact dist_two hconn hB h.symm (fun h' => key h'.symm) hyx
  have hall : ∀ w ∈ insert (l.getD (p - 1) x₀) (insert (l.getD (p + 3) x₀) S), G.dist x₀ w = 2 := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact dist_two hconn hA.symm hAa.symm (fun h' => hna h'.symm) hne_a
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact dist_two hconn hB hBb hnb hne_b
    · exact hSd w hw
  have hc := card_le_gamma hconn hH x₀ _ hall
  have hAS : l.getD (p - 1) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  have hBS : l.getD (p + 3) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  rw [Finset.card_insert_of_notMem (by rw [Finset.mem_insert]; rintro (h | h); exacts [hab h, hAS h]),
    Finset.card_insert_of_notMem hBS] at hc
  omega
-- <</B17>>

-- <<B10>>
lemma b10_side [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y z : V) (hy : y ∉ l) (hz : z ∉ l) (hyz : G.Adj y z)
    (hNy : ∀ w, w ∉ l → G.Adj y w → w = z) :
    (∀ i, i < l.length → G.Adj z (l.getD i x₀) → G.Adj y (l.getD i x₀)) ∧
    secondSmallestDegree G = ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).card + 1 ∧
    ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).filter (fun j => j + 2 ∈ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))))).card + 1 =
      ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).card) := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, rfl⟩
  rw [← hJ]
  have hjb : ∀ j ∈ J, 0 < j ∧ j + 1 < l.length := by
    intro j hj
    rw [hJ] at hj
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hj
  have h0 : 0 ∉ J := fun h => (Nat.lt_irrefl 0) (hjb 0 h).1
  have hdeg := Cadre.degree_split hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
  rw [← hJ] at hdeg
  have hR : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) = {z} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, hadj⟩; exact hNy w hw hadj
    · rintro rfl; exact ⟨hz, hyz⟩
  rw [hR, Finset.card_singleton] at hdeg
  have hy0 : y ≠ x₀ := fun h => hy (h ▸ hmem)
  have hdy := hx0 y hy0
  have hσ2 := sigma_ge hδ
  obtain ⟨Bp, hBp⟩ : ∃ Bp : Finset V, Bp = Finset.univ.filter (fun w => w ∈ l ∧ ¬ G.Adj y w ∧ G.Adj z w) := ⟨_, rfl⟩
  have hQ := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy Bp ∅
    (by
      intro w hw
      rw [hBp] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact ⟨hw.1, hw.2.1, z, hz, hyz, hw.2.2⟩)
    (by intro w hw; simp at hw)
  rw [← hJ] at hQ
  simp only [Finset.card_empty] at hQ
  have hring := ring_card J h0
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  have hT := T_lt J hJne
  have hBp0 : Bp.card = 0 := by omega
  refine ⟨?_, by omega, by omega⟩
  intro i hi hadj
  by_contra hn
  have hmemBp : l.getD i x₀ ∈ Bp := by
    rw [hBp]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hn, hadj⟩
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  rw [Finset.card_eq_zero.mp hBp0] at hmemBp
  simp at hmemBp

lemma Cadre.no_edge_comp [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y z : V) (hy : y ∉ l) (hz : z ∉ l) (hyz : G.Adj y z)
    (hNy : ∀ w, w ∉ l → G.Adj y w → w = z) (hNz : ∀ w, w ∉ l → G.Adj z w → w = y) : False := by
  classical
  obtain ⟨hs1, hσ1, ht1⟩ := b10_side hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y z hy hz hyz hNy
  obtain ⟨hs2, -, -⟩ := b10_side hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt z y hz hy hyz.symm hNz
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, rfl⟩
  rw [← hJ] at hσ1 ht1
  have hjb : ∀ j ∈ J, 0 < j ∧ j + 1 < l.length := by
    intro j hj
    rw [hJ] at hj
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hj
  have hJmem : ∀ j, j ∈ J ↔ j < l.length ∧ G.Adj y (l.getD j x₀) := by
    intro j; rw [hJ]; simp only [Finset.mem_filter, Finset.mem_range]
  have hσ2 := sigma_ge hδ
  -- trous : x_{j+1} = x₀
  have hxj : ∀ j ∈ J.filter (fun j => j + 2 ∈ J), l.getD (j + 1) x₀ = x₀ := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjJ, hj2⟩ := hj
    by_contra hne1
    obtain ⟨hjl, hjadj⟩ := (hJmem j).mp hjJ
    obtain ⟨hj2l, hj2adj⟩ := (hJmem (j + 2)).mp hj2
    exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, z] (by simp)
      (by simp; exact G.ne_of_adj hyz) (by simp [hyz])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption) j (j + 2) (by omega) hj2l
      (by simpa using hjadj.symm) (by simpa using hs2 (j + 2) hj2l hj2adj)
      (by intro i h1 h2; have : i = j + 1 := by omega
          subst this; exact hne1) (by simp)
  have hT1 : (J.filter (fun j => j + 2 ∈ J)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb'
    have ha' := hxj a ha
    have hb'' := hxj b hb'
    have haJ := (Finset.mem_filter.mp ha)
    have hbJ := (Finset.mem_filter.mp hb')
    have hal := (hjb a haJ.1).2
    have hbl := (hjb b hbJ.1).2
    have e1 := ha'
    have e2 := hb''
    rw [List.getD_eq_getElem _ _ hal] at e1
    rw [List.getD_eq_getElem _ _ hbl] at e2
    have := (List.Nodup.getElem_inj_iff hnd).mp (e1.trans e2.symm)
    omega
  have hcpos : 0 < J.card := by omega
  have hc : J.card = 1 ∨ J.card = 2 := by omega
  rcases hc with hc | hc
  · -- sigma = 2
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hpJ : p ∈ J := by rw [hp]; exact Finset.mem_singleton_self p
    obtain ⟨hpl, hpadj⟩ := (hJmem p).mp hpJ
    obtain ⟨hp0, hp1⟩ := hjb p hpJ
    have hxp : l.getD p x₀ ∈ l := by rw [List.getD_eq_getElem _ _ hpl]; exact List.getElem_mem _
    have hidx : ∀ i, i < l.length → G.Adj y (l.getD i x₀) → i = p := by
      intro i hi hadj
      have : i ∈ J := (hJmem i).mpr ⟨hi, hadj⟩
      rw [hp] at this; exact Finset.mem_singleton.mp this
    refine cut_closed hb (l.getD p x₀) {y, z} ?_ ⟨y, by simp⟩ ?_ ?_
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hy (h ▸ hxp)
      · exact hz (h ▸ hxp)
    · intro v hv w hvw hwc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      by_cases hwl : w ∈ l
      · exfalso
        obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hwl
        have hgi : l.getD i x₀ = w := by rw [List.getD_eq_getElem _ _ hi, hiw]
        rcases hv with rfl | rfl
        · have := hidx i hi (by rw [hgi]; exact hvw)
          apply hwc; rw [← hgi, this]
        · have := hidx i hi (hs1 i hi (by rw [hgi]; exact hvw))
          apply hwc; rw [← hgi, this]
      · rcases hv with rfl | rfl
        · exact Or.inr (hNy w hwl hvw)
        · exact Or.inl (hNz w hwl hvw)
    · refine ⟨l.getD 0 x₀, ?_, ?_⟩
      · intro h
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hpl] at h
        have h' := (List.Nodup.getElem_inj_iff hnd).mp h
        omega
      · have h0l : l.getD 0 x₀ ∈ l := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        intro h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact hy (h ▸ h0l)
        · exact hz (h ▸ h0l)
  · -- sigma = 3
    have htc : (J.filter (fun j => j + 2 ∈ J)).card = 1 := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (J.filter (fun j => j + 2 ∈ J)).card)
    have hxj' := hxj j hj
    obtain ⟨hjJ, hj2⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjl, hjadj⟩ := (hJmem j).mp hjJ
    obtain ⟨hj2l, hj2adj⟩ := (hJmem (j + 2)).mp hj2
    obtain ⟨hj0, -⟩ := hjb j hjJ
    obtain ⟨-, hj3⟩ := hjb (j + 2) hj2
    have hres := Cadre.hole_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {y, z}
      (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl <;> assumption) j hj0 (by omega) hxj'
      (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact Or.inl hjadj
          · exact Or.inl (hs2 j hjl hjadj))
      [y, z] (by simp) (by simp; exact G.ne_of_adj hyz) (by simp [hyz])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      (by simpa using hjadj.symm) (by simpa using hs2 (j + 2) hj2l hj2adj)
    rw [Finset.card_pair (G.ne_of_adj hyz)] at hres
    omega
-- <</B10>>

-- <<B11>>
lemma Cadre.Rdeg2 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y : V) (hy : y ∉ l) : 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card := by
  classical
  by_contra hlt2
  push Not at hlt2
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, rfl⟩
  have hjb : ∀ j ∈ J, 0 < j ∧ j + 1 < l.length := by
    intro j hj
    rw [hJ] at hj
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hj
  have h0 : 0 ∉ J := fun h => (Nat.lt_irrefl 0) (hjb 0 h).1
  have hdeg := Cadre.degree_split hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
  rw [← hJ] at hdeg
  have hy0 : y ≠ x₀ := fun h => hy (h ▸ hmem)
  have hdy := hx0 y hy0
  have hσ2 := sigma_ge hδ
  have hring := ring_card J h0
  have hk : ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card = 0 ∨
      ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card = 1 := by omega
  rcases hk with hk | hk
  · have hQ := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy ∅ ∅
      (by intro w hw; simp at hw) (by intro w hw; simp at hw)
    rw [← hJ] at hQ
    simp only [Finset.card_empty] at hQ
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    have hT := T_lt J hJne
    omega
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hk
    have hzmem : z ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) := by rw [hz]; exact Finset.mem_singleton_self z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzmem
    have hNy : ∀ w, w ∉ l → G.Adj y w → w = z := by
      intro w hw hadj
      have : w ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hw, hadj⟩
      rw [hz] at this; exact Finset.mem_singleton.mp this
    by_cases hex : ∃ w, w ∉ l ∧ G.Adj z w ∧ w ≠ y
    · obtain ⟨w, hwl, hzw, hwy⟩ := hex
      have hnadj : ¬ G.Adj y w := by
        intro h
        have := hNy w hwl h
        subst this
        exact G.loopless.irrefl _ hzw
      have hQ := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy ∅ {w}
        (by intro w hw; simp at hw)
        (by intro w' hw'; rw [Finset.mem_singleton] at hw'; subst hw'; exact ⟨hwl, hwy, hnadj, z, hzmem.2, hzw⟩)
      rw [← hJ] at hQ
      simp only [Finset.card_empty, Finset.card_singleton] at hQ
      have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
      have hT := T_lt J hJne
      omega
    · push Not at hex
      exact Cadre.no_edge_comp hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y z hy hzmem.1 hzmem.2 hNy
        hex
-- <</B11>>

-- <<B12>>
lemma Cadre.m_ge [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    2 * secondSmallestDegree G + 2 ≤ l.length := by
  classical
  by_contra hcon
  push Not at hcon
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  set σ := secondSmallestDegree G with hσ
  set a := l.head hne with ha
  set b := l.getLast hne with hbd
  set m := l.length with hm
  have hm2 : 2 ≤ m := by
    by_contra h2
    have h1 : m = 1 := by have := List.length_pos_of_ne_nil hne; omega
    obtain ⟨e, he⟩ := List.length_eq_one_iff.mp h1
    subst he
    simp at hmem hhd
    exact hhd hmem.symm
  obtain ⟨hNa, hNb, hsum, hdisj, hSd, hTd⟩ := lemma4x hconn l hne hnd hch hhs hlt hm2
  simp only [← ha, ← hbd] at hNa hNb hsum hdisj hSd hTd
  have hxa : σ ≤ G.degree a := hx0 a hhd
  have hxb : σ ≤ G.degree b := hx0 b hlast
  have hsum' : G.degree a + G.degree b + 1 ≤ m := hsum
  have hmσ : m = 2 * σ + 1 := by omega
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
  have hNa' : ∀ y, y ∉ l → ¬ G.Adj a y := fun y hy h => hy (hNa y h)
  have hyN : ∀ y, y ∉ l → ∀ j, (hj : j < m) → G.Adj y (f j) → G.Adj a (f j) ∧ f j ≠ a := by
    intro y hy j hj hw
    have hy' : l.getD j y = f j := by
      rw [List.getD_eq_getElem _ _ hj, hf_get j hj]
    obtain ⟨h0, h1, -, -, -, h6⟩ := lemma5abx hconn l hne hnd hch hhs y hy j hj
      (by rw [hy']; exact hw)
    have hy1 : l.getD (j - 1) y = f (j - 1) := by
      rw [List.getD_eq_getElem _ _ (by omega), hf_get (j - 1) (by omega)]
    rw [← hbd, hy1] at h6
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
  have hdist2 : ∀ y, y ∉ l → ∀ j, (hj : j < m) → G.Adj y (f j) → G.dist a y = 2 := by
    intro y hy j hj hadj
    obtain ⟨h1, -⟩ := hyN y hy j hj hadj
    refine dist_two hconn h1 hadj.symm (hNa' y hy) ?_
    intro h
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
  have hTim : ∀ k, k < m → k ≠ 0 → ¬ G.Adj a (f k) → f k ∈ Timg := by
    intro k hk hk0 hna
    rcases hpart (k - 1) (by omega) with h | h
    · rw [show k - 1 + 1 = k by omega] at h; exact absurd h hna
    · exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), h⟩, by rw [show k - 1 + 1 = k by omega]⟩
  set U := Finset.univ.filter (fun w => 2 ≤ G.dist a w) with hU
  set Rs := Finset.univ.filter (fun t => t ∉ l) with hRs
  have hRU : Rs ∪ Timg ⊆ U := by
    intro u hu
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hu with h | h
    · have hul : u ∉ l := by simpa [hRs] using h
      apply hd2
      · intro h'; exact hul (by rw [h']; exact List.head_mem hne)
      · exact hNa' u hul
    · exact hTimg_d u h
  have hdisjRT : Disjoint Rs Timg :=
    Finset.disjoint_left.mpr (fun u h1 h2 => by simp [hRs] at h1; exact h1 (hTimg_l u h2))
  have hUcard : Rs.card + σ ≤ U.card := by
    have := Finset.card_le_card hRU
    rw [Finset.card_union_of_disjoint hdisjRT, hTi_card] at this
    exact this
  set F := Finset.univ.filter (fun w => 3 ≤ G.dist a w ∧ Odd (G.dist a w)) with hF
  set R₀ := Rs.filter (fun y => ∀ j, j < m → ¬ G.Adj y (f j)) with hR₀
  have hFsub : F ⊆ insert x₀ R₀ := by
    intro w hwF
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hwF
    obtain ⟨hw3, -⟩ := hwF
    rw [Finset.mem_insert]
    by_cases hwl : w ∈ l
    · left
      obtain ⟨k, hk, rfl⟩ := hf_ex w hwl
      have hk0 : k ≠ 0 := by rintro rfl; rw [hf0] at hw3; simp at hw3
      have hna : ¬ G.Adj a (f k) := fun h => by
        have := SimpleGraph.dist_eq_one_iff_adj.mpr h; omega
      have hwT : f k ∈ Timg := hTim k hk hk0 hna
      by_contra hwx
      have hdeg := hx0 (f k) hwx
      have hnb : G.neighborFinset (f k) ⊆ Timg.erase (f k) := by
        intro u hu
        rw [SimpleGraph.mem_neighborFinset] at hu
        have hu2 := lemma3a hconn a (f k) hw3 u hu
        rw [Finset.mem_erase]
        refine ⟨hu.ne.symm, ?_⟩
        by_cases hul : u ∈ l
        · obtain ⟨k', hk', rfl⟩ := hf_ex u hul
          have hk0' : k' ≠ 0 := by rintro rfl; rw [hf0] at hu2; simp at hu2
          apply hTim k' hk' hk0'
          intro h
          have := SimpleGraph.dist_eq_one_iff_adj.mpr h; omega
        · exfalso
          exact hna (hyN u hul k hk hu.symm).1
      have hdw := Finset.card_le_card hnb
      rw [Finset.card_erase_of_mem hwT, hTi_card, SimpleGraph.card_neighborFinset_eq_degree] at hdw
      have hpos : 0 < Timg.card := Finset.card_pos.mpr ⟨_, hwT⟩
      omega
    · right
      simp only [hR₀, hRs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hwl, fun j hj hadj => ?_⟩
      have := hdist2 w hwl j hj hadj
      omega
  have h3b : U.card ≤ σ + F.card := lemma3b hconn a (hH a)
  have hFc : F.card ≤ R₀.card + 1 := by
    have h1 := Finset.card_le_card hFsub
    have h2 := Finset.card_insert_le x₀ R₀
    omega
  obtain ⟨v, hv, y, hy, hvy⟩ := exists_out_edge hconn l hne hnd hlt
  have hyRs : y ∈ Rs := by simp [hRs, hy]
  have h2y := Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy
  have hR3 : 3 ≤ Rs.card := by
    have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) ⊆ Rs.erase y := by
      intro w hw
      rw [Finset.mem_erase]
      refine ⟨?_, (Finset.mem_filter.mp hw).1⟩
      rintro rfl
      exact G.loopless.irrefl _ (Finset.mem_filter.mp hw).2
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hyRs] at this
    omega
  set R₁ := Rs.filter (fun y => ¬ ∀ j, j < m → ¬ G.Adj y (f j)) with hR₁
  have hsplit : R₀.card + R₁.card = Rs.card := Finset.card_filter_add_card_filter_not _
  have hR1le : R₁.card ≤ 1 := by omega
  have hyR1 : y ∈ R₁ := by
    obtain ⟨j, hj, rfl⟩ := hf_ex v hv
    simp only [hR₁, Finset.mem_filter]
    exact ⟨hyRs, fun h => h j hj hvy.symm⟩
  have hR1eq : ∀ w ∈ R₁, w = y := fun w hw =>
    Finset.card_le_one.mp hR1le w hw y hyR1
  have hy0 : y ∉ R₀ := by
    intro h
    simp only [hR₀, Finset.mem_filter] at h
    simp only [hR₁, Finset.mem_filter] at hyR1
    exact hyR1.2 h.2
  have hR0pos : R₀.Nonempty := Finset.card_pos.mp (by omega)
  refine cut_closed hb y R₀ hy0 hR0pos ?_ ⟨a, ?_, ?_⟩
  · intro w hw w' hww' hw'y
    simp only [hR₀, Finset.mem_filter] at hw
    by_cases hwl : w' ∈ l
    · obtain ⟨j, hj, rfl⟩ := hf_ex w' hwl
      exact absurd hww' (hw.2 j hj)
    · by_contra hn
      have hw'R : w' ∈ R₁ := by
        simp only [hR₁, hR₀, Finset.mem_filter] at hn ⊢
        have hw'Rs : w' ∈ Rs := by simp [hRs, hwl]
        exact ⟨hw'Rs, fun h => hn ⟨hw'Rs, h⟩⟩
      exact hw'y (hR1eq w' hw'R)
  · intro h
    exact hy (by rw [← h]; exact List.head_mem hne)
  · intro h
    simp only [hR₀, hRs, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h.1 (List.head_mem hne)
-- <</B12>>

-- <<B13>>
lemma Cadre.two_attach [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ∃ a b, a < b ∧ b < l.length ∧ (∃ y ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y (l.getD a x₀)) ∧
      (∃ y ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y (l.getD b x₀)) := by
  classical
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  obtain ⟨v, hv, y, hy, hvy⟩ := exists_out_edge hconn l hne hnd hlt
  obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hv
  have hga : ∀ i (h : i < l.length), l.getD i x₀ = l[i] := fun i h => List.getD_eq_getElem _ _ h
  have hyR : y ∈ Finset.univ.filter (fun t => t ∉ l) := by simp [hy]
  by_cases hother : ∃ b y', b < l.length ∧ b ≠ a ∧ y' ∉ l ∧ G.Adj y' (l.getD b x₀)
  · obtain ⟨b, y', hb', hba, hy', hadj'⟩ := hother
    have hy'R : y' ∈ Finset.univ.filter (fun t => t ∉ l) := by simp [hy']
    rcases lt_or_gt_of_ne hba with h | h
    · exact ⟨b, a, h, ha, ⟨y', hy'R, hadj'⟩, ⟨y, hyR, by rw [hga a ha]; exact hvy.symm⟩⟩
    · exact ⟨a, b, h, hb', ⟨y, hyR, by rw [hga a ha]; exact hvy.symm⟩, ⟨y', hy'R, hadj'⟩⟩
  · exfalso
    push Not at hother
    have ha0 : 0 < a := (lemma5abx hconn l hne hnd hch hhs y hy a ha
      (by rw [List.getD_eq_getElem _ _ ha]; exact hvy.symm)).1
    refine cut_closed hb l[a] (Finset.univ.filter (fun t => t ∉ l)) (by simp) ⟨y, hyR⟩ ?_ ?_
    · intro v' hv' w hvw hwc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv' ⊢
      intro hwl
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hwl
      have hia : i ≠ a := by
        rintro rfl; exact hwc rfl
      exact hother i v' hi hia hv' (by rw [hga i hi]; exact hvw)
    · refine ⟨l.getD 0 x₀, ?_, ?_⟩
      · rw [hga 0 (by omega)]
        intro h
        have := (List.Nodup.getElem_inj_iff hnd).mp h
        omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
        rw [hga 0 (by omega)]; exact List.getElem_mem _
-- <</B13>>

-- <<B14.R_ge3>>
lemma b14_rcard {l : List V} (hnd : l.Nodup) (hlt : l.length < Fintype.card V) :
    ((Finset.univ.filter (fun t => t ∉ l))).card + l.length = Fintype.card V := by
  have h : Finset.univ.filter (fun t => t ∉ l) = (l.toFinset)ᶜ := by
    ext t; simp
  rw [h, Finset.card_compl, List.toFinset_card_of_nodup hnd]
  omega

lemma Cadre.R_ge3 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    3 ≤ ((Finset.univ.filter (fun t => t ∉ l))).card := by
  classical
  have hc := b14_rcard hnd hlt
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.filter (fun t => t ∉ l))).card)
  have hyl : y ∉ l := by simpa using hy
  have h2 := Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hyl
  have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) ⊆ (Finset.univ.filter (fun t => t ∉ l)).erase y := by
    intro w hw
    rw [Finset.mem_erase]
    refine ⟨?_, (Finset.mem_filter.mp hw).1⟩
    rintro rfl
    exact G.loopless.irrefl _ (Finset.mem_filter.mp hw).2
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hy] at this
  omega
-- <</B14.R_ge3>>

-- <<B14.R_card>>
lemma Cadre.R_card [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ((Finset.univ.filter (fun t => t ∉ l))).card + l.length = Fintype.card V := by
  exact b14_rcard hnd hlt
-- <</B14.R_card>>

-- <<B14.R3>>
lemma b14_two [DecidableRel G.Adj] {l : List V} {x c d : V}
    (hx : 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj x)).card)
    (hE : ∀ w, w ∉ l → G.Adj x w → w = c ∨ w = d) (hcd : c ≠ d) : G.Adj x c ∧ G.Adj x d := by
  have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj x) ⊆ {c, d} := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simpa using hE w hw.1 hw.2
  have hcard : ({c, d} : Finset V).card = 2 := Finset.card_pair hcd
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hc : c ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj x) := by rw [heq]; simp
  have hd : d ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj x) := by rw [heq]; simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hd
  exact ⟨hc.2, hd.2⟩

lemma Cadre.R3 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (h : ((Finset.univ.filter (fun t => t ∉ l))).card = 3) :
    ∃ u v w : V, (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w} ∧ u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
      G.Adj u v ∧ G.Adj v w ∧ G.Adj u w := by
  have hR2 : ∀ y, y ∉ l → 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card :=
    fun y hy => Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy
  obtain ⟨u, v, w, huv, huw, hvw, hR⟩ := Finset.card_eq_three.mp h
  have hmemR : ∀ t, t ∈ (Finset.univ.filter (fun t => t ∉ l)) ↔ t ∉ l := by intro t; simp
  have hu : u ∉ l := (hmemR u).mp (by rw [hR]; simp)
  have hv : v ∉ l := (hmemR v).mp (by rw [hR]; simp)
  have hw : w ∉ l := (hmemR w).mp (by rw [hR]; simp)
  have hE : ∀ x, ∀ t, t ∉ l → G.Adj x t → t ∈ ({u, v, w} : Finset V) := by
    intro x t ht _
    rw [← hR]; exact (hmemR t).mpr ht
  have hu' := b14_two (hR2 u hu) (c := v) (d := w) (fun t ht hadj => by
    have := hE u t ht hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | h | h
    · exact absurd hadj (G.loopless.irrefl _)
    · exact Or.inl h
    · exact Or.inr h) hvw
  have hv' := b14_two (hR2 v hv) (c := u) (d := w) (fun t ht hadj => by
    have := hE v t ht hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | rfl | h
    · exact Or.inl h
    · exact absurd hadj (G.loopless.irrefl _)
    · exact Or.inr h) huw
  exact ⟨u, v, w, hR, huv, hvw, huw, hu'.1, hv'.2, hu'.2⟩
-- <</B14.R3>>

-- <<B14.R4>>
lemma b14_right [DecidableRel G.Adj] {l : List V}
    (hR2 : ∀ y, y ∉ l → 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card)
    (p p' a b : V) (hset : Finset.univ.filter (fun t => t ∉ l) = {p, p', a, b})
    (h1 : p ≠ p') (h2 : p ≠ a) (h3 : p ≠ b) (h4 : p' ≠ a) (h5 : p' ≠ b) (h6 : a ≠ b)
    (hn : ¬ G.Adj p p') :
    ∃ z z' a b : V, (Finset.univ.filter (fun t => t ∉ l)) = {z, z', a, b} ∧ z ≠ z' ∧ z ≠ a ∧ z ≠ b ∧ z' ≠ a ∧ z' ≠ b ∧ a ≠ b ∧
      ¬ G.Adj z z' ∧ G.Adj z a ∧ G.Adj z b ∧ G.Adj z' a ∧ G.Adj z' b := by
  have hmemR : ∀ t, t ∈ Finset.univ.filter (fun t => t ∉ l) ↔ t ∉ l := by intro t; simp
  have hp : p ∉ l := (hmemR p).mp (by rw [hset]; simp)
  have hp' : p' ∉ l := (hmemR p').mp (by rw [hset]; simp)
  have hE : ∀ t, t ∉ l → t = p ∨ t = p' ∨ t = a ∨ t = b := by
    intro t ht
    have : t ∈ ({p, p', a, b} : Finset V) := by rw [← hset]; exact (hmemR t).mpr ht
    simpa using this
  have e1 := b14_two (hR2 p hp) (c := a) (d := b) (fun t ht hadj => by
    rcases hE t ht with h | h | h | h
    · rw [h] at hadj; exact absurd hadj (G.loopless.irrefl _)
    · rw [h] at hadj; exact absurd hadj hn
    · exact Or.inl h
    · exact Or.inr h) h6
  have e2 := b14_two (hR2 p' hp') (c := a) (d := b) (fun t ht hadj => by
    rcases hE t ht with h | h | h | h
    · rw [h] at hadj; exact absurd hadj.symm hn
    · rw [h] at hadj; exact absurd hadj (G.loopless.irrefl _)
    · exact Or.inl h
    · exact Or.inr h) h6
  exact ⟨p, p', a, b, hset, h1, h2, h3, h4, h5, h6, hn, e1.1, e1.2, e2.1, e2.2⟩

lemma Cadre.R4 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (h : ((Finset.univ.filter (fun t => t ∉ l))).card = 4) :
    (∃ a b c d : V, (Finset.univ.filter (fun t => t ∉ l)) = {a, b, c, d} ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d) ∨
    (∃ z z' a b : V, (Finset.univ.filter (fun t => t ∉ l)) = {z, z', a, b} ∧ z ≠ z' ∧ z ≠ a ∧ z ≠ b ∧ z' ≠ a ∧ z' ≠ b ∧ a ≠ b ∧
      ¬ G.Adj z z' ∧ G.Adj z a ∧ G.Adj z b ∧ G.Adj z' a ∧ G.Adj z' b) := by
  have hR2 : ∀ y, y ∉ l → 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card :=
    fun y hy => Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hR⟩ := Finset.card_eq_four.mp h
  by_cases hall : G.Adj x y ∧ G.Adj x z ∧ G.Adj x w ∧ G.Adj y z ∧ G.Adj y w ∧ G.Adj z w
  · left
    exact ⟨x, y, z, w, hR, hxy, hxz, hxw, hyz, hyw, hzw, hall.1, hall.2.1, hall.2.2.1,
      hall.2.2.2.1, hall.2.2.2.2.1, hall.2.2.2.2.2⟩
  · right
    have hn : ¬G.Adj x y ∨ ¬G.Adj x z ∨ ¬G.Adj x w ∨ ¬G.Adj y z ∨ ¬G.Adj y w ∨ ¬G.Adj z w := by
      tauto
    rcases hn with hn | hn | hn | hn | hn | hn
    · exact b14_right hR2 x y z w hR hxy hxz hxw hyz hyw hzw hn
    · exact b14_right hR2 x z y w (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hxz hxy hxw hyz.symm hzw hyw hn
    · exact b14_right hR2 x w y z (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hxw hxy hxz hyw.symm hzw.symm hyz hn
    · exact b14_right hR2 y z x w (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hyz hxy.symm hyw hxz.symm hzw hxw hn
    · exact b14_right hR2 y w x z (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hyw hxy.symm hyz hxw.symm hzw.symm hxz hn
    · exact b14_right hR2 z w x y (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hzw hxz.symm hyz.symm hxw.symm hyw.symm hxy hn
-- <</B14.R4>>

-- <<B15>>
lemma Cadre.small_sigma [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hham : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∃ s : List V, s.Nodup ∧ s.IsChain G.Adj ∧ s.toFinset = (Finset.univ.filter (fun t => t ∉ l)) ∧
      s.getLast? = some y)
    (hd2 : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∀ y' ∈ (Finset.univ.filter (fun t => t ∉ l)), y ≠ y' →
      G.Adj y y' ∨ ∃ w ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y w ∧ G.Adj w y') :
    ((Finset.univ.filter (fun t => t ∉ l))).card + 5 ≤ l.length := by
  classical
  obtain ⟨a, b, hab, hbl, ⟨y, hy, hya⟩, ⟨y', hy', hyb⟩⟩ :=
    Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hyl : y ∉ l := (Finset.mem_filter.1 hy).2
  have hyl' : y' ∉ l := (Finset.mem_filter.1 hy').2
  obtain ⟨i₀, hi₀, hxi⟩ := List.mem_iff_getElem.1 hmem
  have hxi' : l.getD i₀ x₀ = x₀ := by rw [List.getD_eq_getElem _ _ hi₀]; exact hxi
  have hi0pos : i₀ ≠ 0 := by
    intro h; subst h; apply hhd; rw [b15_head hne x₀]; exact hxi'
  have hi0last : i₀ ≠ l.length - 1 := by
    intro h; apply hlast; rw [b15_last hne x₀, ← h]; exact hxi'
  have hnx : ∀ i, i < l.length → i ≠ i₀ → l.getD i x₀ ≠ x₀ :=
    fun i hi hne' h => hne' (b15_inj x₀ hnd hi hi₀ (h.trans hxi'.symm))
  have hr3 : 3 ≤ (Finset.univ.filter (fun t => t ∉ l)).card := by
    have h2 := Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hyl
    have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) ⊆
        (Finset.univ.filter (fun t => t ∉ l)).erase y := by
      intro v hv
      rw [Finset.mem_filter] at hv
      exact Finset.mem_erase.2 ⟨fun h => G.loopless.irrefl y (h ▸ hv.2), hv.1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hy] at this
    omega
  have hpath : ∀ z ∈ Finset.univ.filter (fun t => t ∉ l), ∃ s : List V, ∃ hs : s ≠ [], s.Nodup ∧
      s.IsChain G.Adj ∧ (∀ v ∈ s, v ∉ l) ∧ s.getLast hs = z ∧
      s.length = (Finset.univ.filter (fun t => t ∉ l)).card := by
    intro z hz
    obtain ⟨s, snd, sch, hsR, hsl⟩ := hham z hz
    have hs : s ≠ [] := by intro h; rw [h] at hsl; simp at hsl
    refine ⟨s, hs, snd, sch, ?_, ?_, ?_⟩
    · intro v hv
      have : v ∈ s.toFinset := List.mem_toFinset.2 hv
      rw [hsR] at this
      exact (Finset.mem_filter.1 this).2
    · have := List.getLast?_eq_getLast hs
      rw [hsl] at this
      exact (Option.some.inj this).symm
    · rw [← hsR]; exact (List.toFinset_card_of_nodup snd).symm
  have hL : i₀ < a ∨ (Finset.univ.filter (fun t => t ∉ l)).card ≤ a := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs, snd, sch, sl, hlast_eq, hslen⟩ := hpath y hy
    exact Cadre.no_pre hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch sl a
      (by omega) (by rw [hlast_eq]; exact hya) (fun i hi => hnx i (by omega) (by omega)) (by omega)
  have hRr : b < i₀ ∨ (Finset.univ.filter (fun t => t ∉ l)).card ≤ l.length - 1 - b := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs, snd, sch, sl, hlast_eq, hslen⟩ := hpath y' hy'
    have hs' : s.reverse ≠ [] := by simpa using hs
    have hhead : s.reverse.head hs' = y' := by rw [List.head_reverse]; exact hlast_eq
    exact Cadre.no_suf hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s.reverse hs'
      (List.nodup_reverse.2 snd) (chain_rev sch) (fun v hv => sl v (List.mem_reverse.1 hv)) b hbl
      (by rw [hhead]; exact hyb.symm) (fun i h1 h2 => hnx i h2 (by omega))
      (by rw [List.length_reverse]; omega)
  have hM : a + 2 ≤ b := by
    by_contra hcon
    have hb1 : b = a + 1 := by omega
    by_cases hyy : y = y'
    · subst hyy
      exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y]
        (by simp) (by simp) (by simp) (by simpa using hyl) a b hab hbl (by simpa using hya.symm)
        (by simpa using hyb) (fun i h1 h2 => absurd h2 (by omega)) (by simp; omega)
    · by_cases hadj : G.Adj y y'
      · exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, y']
          (by simp) (by simp [hyy]) (by simp [hadj]) (by simp [hyl, hyl']) a b hab hbl
          (by simpa using hya.symm) (by simpa using hyb) (fun i h1 h2 => absurd h2 (by omega))
          (by simp; omega)
      · obtain ⟨w, hw, hyw, hwy'⟩ := (hd2 y hy y' hy' hyy).resolve_left hadj
        have hwl : w ∉ l := (Finset.mem_filter.1 hw).2
        exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, w, y']
          (by simp)
          (by simp [hyy, hyw.ne, hwy'.ne])
          (by simp [hyw, hwy'])
          (by simp [hyl, hwl, hyl']) a b hab hbl
          (by simpa using hya.symm) (by simpa using hyb) (fun i h1 h2 => absurd h2 (by omega))
          (by simp; omega)
  omega
-- <</B15>>

-- <<B16>>
lemma b16_inv (E : Finset ℕ) (K i₀ : ℕ) (s : Finset ℕ) :
    (∀ x ∈ s, 1 ≤ x) → ((∀ x ∈ s, K + 1 ≤ x) ∨ (∀ x ∈ s, i₀ < x)) →
    (∀ a ∈ s, ∀ b ∈ s, a < b → (∀ c ∈ s, ¬ (a < c ∧ c < b)) →
      a + 2 ≤ b ∧ (a ∉ E → a + (K + 1) + 1 ≤ b ∨ (a < i₀ ∧ i₀ < b))) →
    ∀ a ∈ s, (∀ x ∈ s, x ≤ a) →
      (K + 2) * s.card ≤ a + 1 + K * (((s.erase a).filter (· ∈ E)).card + if i₀ < a then 1 else 0) := by
  induction s using Finset.induction_on_max with
  | empty => intro _ _ _ a ha; simp at ha
  | insert a s hlt ih =>
    intro h1 hL hM a' ha' hmax'
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ea : a = a' := by
      have h3 := hmax' a (Finset.mem_insert_self _ _)
      rcases Finset.mem_insert.1 ha' with h | h
      · exact h.symm
      · have := hlt a' h; omega
    subst ea
    rw [Finset.card_insert_of_notMem has, Finset.erase_insert has]
    rcases s.eq_empty_or_nonempty with rfl | hne
    · have h0 := h1 a (Finset.mem_insert_self _ _)
      simp only [Finset.card_empty, Finset.filter_empty, zero_add]
      rcases hL with hL | hL
      · have := hL a (Finset.mem_insert_self _ _)
        split_ifs <;> simp <;> nlinarith
      · have := hL a (Finset.mem_insert_self _ _)
        rw [if_pos this]
        simp only [Finset.card_empty, mul_one]
        nlinarith
    · obtain ⟨m0, hm0, hm0max⟩ := Finset.exists_max_image s id hne
      have ih' := ih (fun x hx => h1 x (Finset.mem_insert_of_mem hx))
        (hL.imp (fun h x hx => h x (Finset.mem_insert_of_mem hx))
          (fun h x hx => h x (Finset.mem_insert_of_mem hx)))
        (by
          intro a1 ha1 b1 hb1 hab hno
          refine hM a1 (Finset.mem_insert_of_mem ha1) b1 (Finset.mem_insert_of_mem hb1) hab ?_
          intro c hc
          rcases Finset.mem_insert.1 hc with rfl | hc
          · have := hlt b1 hb1; omega
          · exact hno c hc)
        m0 hm0 (fun x hx => hm0max x hx)
      have hMa := hM m0 (Finset.mem_insert_of_mem hm0) a (Finset.mem_insert_self _ _) (hlt m0 hm0)
        (by
          intro c hc
          rcases Finset.mem_insert.1 hc with rfl | hc
          · omega
          · have := hm0max c hc; simp only [id] at this; omega)
      have hf : (s.filter (· ∈ E)).card = ((s.erase m0).filter (· ∈ E)).card + if m0 ∈ E then 1 else 0 := by
        rw [Finset.filter_erase]
        by_cases hE : m0 ∈ E
        · have hmf : m0 ∈ s.filter (· ∈ E) := Finset.mem_filter.2 ⟨hm0, hE⟩
          rw [Finset.card_erase_of_mem hmf, if_pos hE]
          have := Finset.card_pos.2 ⟨m0, hmf⟩
          omega
        · rw [Finset.erase_eq_of_notMem (fun h => hE (Finset.mem_filter.1 h).2), if_neg hE]; rfl
      rw [hf]
      by_cases hE : m0 ∈ E
      · have h5 := hMa.1
        rw [if_pos hE]
        split_ifs at ih' ⊢ <;> simp only [mul_add, mul_one] at ih' ⊢ <;> omega
      · have h5 := hMa.1
        have h6 := hMa.2 hE
        rw [if_neg hE]
        split_ifs at ih' ⊢ <;> simp only [mul_add, mul_one, add_zero, mul_zero] at ih' ⊢ <;> omega

lemma pack (A E : Finset ℕ) (m k i₀ : ℕ) (hk : 1 ≤ k) (hA : A.Nonempty) (hE : E ⊆ A)
    (hAm : ∀ a ∈ A, 1 ≤ a ∧ a + 2 ≤ m) (hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ m)
    (hL : k ≤ A.min' hA ∨ i₀ < A.min' hA)
    (hR : A.max' hA + k + 1 ≤ m ∨ A.max' hA < i₀)
    (hM : ∀ a ∈ A, ∀ b ∈ A, a < b → (∀ c ∈ A, ¬ (a < c ∧ c < b)) →
        a + 2 ≤ b ∧ (a ∉ E → a + k + 1 ≤ b ∨ (a < i₀ ∧ i₀ < b))) :
    (k + 1) * A.card + 1 ≤ m + (k - 1) * E.card := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  have hLs : (∀ x ∈ A, K + 1 ≤ x) ∨ (∀ x ∈ A, i₀ < x) :=
    hL.imp (fun h x hx => h.trans (A.min'_le x hx)) (fun h x hx => h.trans_le (A.min'_le x hx))
  have hinv := b16_inv E K i₀ A (fun x hx => (hAm x hx).1) hLs hM (A.max' hA) (A.max'_mem hA)
    (fun x hx => A.le_max' x hx)
  have hfe : ((A.erase (A.max' hA)).filter (· ∈ E)).card ≤ E.card :=
    Finset.card_le_card (fun x hx => (Finset.mem_filter.1 hx).2)
  have hKE := Nat.mul_le_mul_left K hfe
  have hmx := (hAm _ (A.max'_mem hA)).2
  simp only [Nat.add_sub_cancel]
  rcases hR with hR | hR
  · split_ifs at hinv <;> simp only [mul_add, mul_one, add_zero, mul_zero] at hinv ⊢ <;> nlinarith
  · rw [if_neg (by omega)] at hinv
    simp only [mul_add, mul_zero, add_zero] at hinv ⊢
    nlinarith
-- <</B16>>


-- <<B18>>
lemma Cadre.x0_attach [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (S : Finset V) (hS : ∀ y ∈ S, y ∉ l) (p : ℕ) (hp : 1 ≤ p) (hp1 : p + 1 < l.length)
    (hx : l.getD p x₀ = x₀) (hSA : ∀ y ∈ S, G.Adj y x₀) :
    S.card + 2 ≤ secondSmallestDegree G := by
  have hmx := deg_x0_le hmin
  have hpl : p < l.length := by omega
  have hA : G.Adj (l.getD (p - 1) x₀) x₀ := by
    have := b15_adj (G := G) x₀ hch (i := p - 1) (by omega)
    rwa [Nat.sub_add_cancel hp, hx] at this
  have hB : G.Adj x₀ (l.getD (p + 1) x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p) (by omega)
    rwa [hx] at this
  have hne1 : l.getD (p - 1) x₀ ≠ l.getD (p + 1) x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) h
    omega
  have hAS : l.getD (p - 1) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  have hBS : l.getD (p + 1) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  have hsub : insert (l.getD (p - 1) x₀) (insert (l.getD (p + 1) x₀) S) ⊆ G.neighborFinset x₀ := by
    intro v hv
    rw [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact hA.symm
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact hB
    · exact (hSA v hv).symm
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by rw [Finset.mem_insert]; rintro (h | h); exacts [hne1 h, hAS h]), Finset.card_insert_of_notMem hBS,
    SimpleGraph.card_neighborFinset_eq_degree] at hc
  omega
-- <</B18>>

-- <<B19>>
lemma b19_perm4 (t seg s d : List V) :
    (t ++ (s ++ (seg.reverse ++ d))).Perm (s ++ (t ++ (seg ++ d))) := by
  refine List.perm_iff_count.2 (fun a => ?_)
  simp only [List.count_append, List.count_reverse]
  omega

lemma b19_split (l : List V) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ l.length) :
    l = l.take i ++ ((l.drop i).take (j - i) ++ l.drop j) := by
  have e : (l.drop i).drop (j - i) = l.drop j := by
    rw [List.drop_drop]; congr 1; omega
  conv_lhs => rw [← List.take_append_drop i l, ← List.take_append_drop (j - i) (l.drop i), e]

lemma b19_seglast (l : List V) (d : V) {p q : ℕ} (hpq : p + 3 ≤ q) (hq : q < l.length) :
    ((l.drop (p + 1)).take (q - p)).getLast? = some (l.getD q d) := by
  rw [List.getLast?_take, if_neg (by omega), List.getElem?_drop,
    show p + 1 + (q - p - 1) = q by omega, List.getElem?_eq_getElem hq,
    List.getD_eq_getElem _ _ hq]
  rfl

lemma b19_seghead (l : List V) (d : V) {p q : ℕ} (hpq : p + 3 ≤ q) (hq : q < l.length) :
    ((l.drop (p + 1)).take (q - p)).head? = some (l.getD (p + 1) d) := by
  rw [List.head?_take, if_neg (by omega), List.head?_drop, List.getElem?_eq_getElem (by omega),
    List.getD_eq_getElem _ _ (by omega)]

lemma Cadre.walk_x0 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l)
    (p q : ℕ) (hp : 1 ≤ p) (hpq : p + 3 ≤ q) (hq : q + 1 < l.length) (hx : l.getD (p + 1) x₀ = x₀)
    (hsp : ∀ y ∈ s, G.Adj y (l.getD p x₀)) (hsq : ∀ y ∈ s, G.Adj y (l.getD q x₀))
    (hσ : secondSmallestDegree G ≤ s.length + 1) (hg : q - p - 1 ≤ s.length) : False := by
  have hmx := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hp2 : p + 2 < l.length := by omega
  have hA : G.Adj (l.getD p x₀) x₀ := by
    have := b15_adj (G := G) x₀ hch (i := p) (by omega)
    rwa [hx] at this
  have hB : G.Adj x₀ (l.getD (p + 2) x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p + 1) (by omega)
    rwa [hx] at this
  have hAa : G.Adj (l.getD (p - 1) x₀) (l.getD p x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p - 1) (by omega)
    rwa [Nat.sub_add_cancel hp] at this
  have hsl := List.getLast?_eq_getLast hs
  have hhs : G.Adj (l.getD p x₀) (s.head hs) := (hsp _ (List.head_mem hs)).symm
  have hls : G.Adj (s.getLast hs) (l.getD q x₀) := hsq _ (List.getLast_mem hs)
  have hne_a : l.getD (p - 1) x₀ ≠ x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
    omega
  have hna : ¬ G.Adj (l.getD (p - 1) x₀) x₀ := by
    intro hadj
    have hd := b17_decomp l x₀ (i := p) (by omega)
    rw [hx] at hd
    have hsub : (l.take p ++ l.getD p x₀ :: x₀ :: l.drop q).Sublist
        (l.take p ++ l.getD p x₀ :: x₀ :: l.drop (p + 2)) :=
      List.Sublist.append (List.Sublist.refl _)
        (List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.drop_sublist_drop_left l (by omega))))
    rw [← hd] at hsub
    have hl''nd := hnd.sublist hsub
    have hperm := b17_perm1 (l.take p) (l.drop q) s (l.getD p x₀) x₀
    have hcnd : (l.take p ++ x₀ :: l.getD p x₀ :: (s ++ l.drop q)).Nodup :=
      hperm.nodup_iff.2 (List.nodup_append.2 ⟨snd, hl''nd, fun a ha b hb h =>
        sl a ha (h ▸ hsub.subset hb)⟩)
    have hchain : (l.take p ++ x₀ :: l.getD p x₀ :: (s ++ l.drop q)).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
      · refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_, List.isChain_append.2 ⟨sch, hch.drop _, ?_⟩⟩⟩
        · intro z hz
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hA.symm
        · intro z hz
          rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hhs
        · intro z hz w hw
          rw [hsl, Option.mem_def, Option.some.injEq] at hz
          rw [b17_head_drop x₀ (by omega), Option.mem_def, Option.some.injEq] at hw
          subst hz hw; exact hls
      · intro z hz w hw
        rw [b17_last_take x₀ hp (by omega), Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        subst hz hw; exact hadj
    have := hmax _ hcnd hchain (List.mem_append_right _ (List.mem_cons_self ..))
    simp only [List.length_append, List.length_cons, List.length_take, List.length_drop] at this
    omega
  have hSd : ∀ y ∈ s, G.dist x₀ y = 2 := by
    intro y hy
    have hyl := sl y hy
    have hyx : y ≠ x₀ := fun h => hyl (h ▸ hmem)
    have hadj' : G.Adj y (l.getD p y) := by
      rw [b15_dflt (l := l) (i := p) (by omega) y x₀]; exact hsp y hy
    obtain ⟨-, -, h5, -, -, -⟩ := lemma5abx hconn l hne hnd hch hmx y hyl p (by omega) hadj'
    exact dist_two hconn hA.symm (hsp y hy).symm
      (fun h' => h5 (by rw [b15_dflt (l := l) (i := p + 1) (by omega) y x₀, hx]; exact h'.symm)) hyx
  have hAS : l.getD (p - 1) x₀ ∉ s.toFinset := fun h =>
    sl _ (List.mem_toFinset.1 h) (b15_mem x₀ (by omega))
  have hS0 : ∀ w ∈ insert (l.getD (p - 1) x₀) s.toFinset, G.dist x₀ w = 2 := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact dist_two hconn hA.symm hAa.symm (fun h' => hna h'.symm) hne_a
    · exact hSd w (List.mem_toFinset.1 hw)
  have hS0c : (insert (l.getD (p - 1) x₀) s.toFinset).card = s.length + 1 := by
    rw [Finset.card_insert_of_notMem hAS, List.toFinset_card_of_nodup snd]
  have hadjall : ∀ i, p + 2 ≤ i → i ≤ q + 1 → G.Adj x₀ (l.getD i x₀) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => intro _; exact hB
    | succ i hi ih =>
      intro hiq
      have ih := ih (by omega)
      by_contra hn
      have hnl : l.getD (i + 1) x₀ ∉ insert (l.getD (p - 1) x₀) s.toFinset := by
        rw [Finset.mem_insert, not_or]
        refine ⟨fun h => ?_, fun h => sl _ (List.mem_toFinset.1 h) (b15_mem x₀ (by omega))⟩
        have := b15_inj x₀ hnd (by omega) (by omega) h
        omega
      have hne' : l.getD (i + 1) x₀ ≠ x₀ := by
        intro h
        have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
        omega
      have hd2' := dist_two hconn ih (b15_adj (G := G) x₀ hch (i := i) (by omega)) hn hne'
      have hc := card_le_gamma hconn hH x₀ (insert (l.getD (i + 1) x₀) (insert (l.getD (p - 1) x₀) s.toFinset))
        (by
          intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw
          · exact hd2'
          · exact hS0 w hw)
      rw [Finset.card_insert_of_notMem hnl, hS0c] at hc
      omega
  have hlast_adj := hadjall (q + 1) (by omega) le_rfl
  have hc4 : ((l.take (p + 1) ++ (s ++ (((l.drop (p + 1)).take (q - p)).reverse ++ l.drop (q + 1))))).IsChain G.Adj := by
    refine List.isChain_append.2 ⟨hch.take _, List.isChain_append.2 ⟨sch,
      List.isChain_append.2 ⟨chain_rev ((hch.drop _).take _), hch.drop _, ?_⟩, ?_⟩, ?_⟩
    · intro z hz w hw
      rw [List.getLast?_reverse, b19_seghead l x₀ (by omega) (by omega), Option.mem_def,
        Option.some.injEq] at hz
      rw [b17_head_drop x₀ (by omega), Option.mem_def, Option.some.injEq] at hw
      subst hz hw
      rw [hx]; exact hlast_adj
    · intro z hz w hw
      rw [hsl, Option.mem_def, Option.some.injEq] at hz
      have hrev : (((l.drop (p + 1)).take (q - p)).reverse ++ l.drop (q + 1)).head? =
          some (l.getD q x₀) := by
        rw [List.head?_append, List.head?_reverse, b19_seglast l x₀ (by omega) (by omega)]
        rfl
      rw [hrev, Option.mem_def, Option.some.injEq] at hw
      subst hz hw; exact hls
    · intro z hz w hw
      have hz' := b17_last_take (l := l) x₀ (p := p + 1) (by omega) (by omega)
      rw [hz', Option.mem_def, Option.some.injEq] at hz
      rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hw
      subst hz hw
      simpa using hhs
  have hperm := b19_perm4 (l.take (p + 1)) ((l.drop (p + 1)).take (q - p)) s (l.drop (q + 1))
  have hsplit := b19_split l (i := p + 1) (j := q + 1) (by omega) (by omega)
  have e1 : q + 1 - (p + 1) = q - p := by omega
  rw [e1] at hsplit
  rw [← hsplit] at hperm
  exact b17_long hnd sl snd hs hmem hmax hperm hc4
-- <</B19>>

-- <<B20.head_deg_le>>
lemma Cadre.head_deg_le [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (C : Finset ℕ)
    (hex : ∀ j, 0 < j → j < l.length → j ∉ C → ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀)) :
    G.degree (l.getD 0 x₀) ≤ C.card := by
  have hmx := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have h2 := b15_len2 hne hmem hhd
  obtain ⟨-, -, -, -, h5, -⟩ := lemma4x hconn l hne hnd hch hmx hlt h2
  have e := b15_head hne x₀
  rw [← e]
  refine h5.trans (Finset.card_le_card_of_injOn (fun j => j + 1) ?_ ?_)
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    show j + 1 ∈ C
    by_contra hC'
    apply hex (j + 1) (by omega) (by omega) hC'
    have := hj.2
    rwa [e, b15_dflt (l := l) (i := j + 1) (by omega) (l.getD 0 x₀) x₀] at this
  · intro a _ b _ h
    simpa using h
-- <</B20.head_deg_le>>

-- <<B20.head_forced>>
lemma Cadre.head_forced [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (C : Finset ℕ) (hCr : ∀ j ∈ C, 0 < j ∧ j < l.length)
    (hex : ∀ j, 0 < j → j < l.length → j ∉ C → ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀))
    (hdeg : C.card ≤ G.degree (l.getD 0 x₀)) :
    ∀ j ∈ C, G.Adj (l.getD 0 x₀) (l.getD j x₀) := by
  intro j hj
  by_contra hadj
  have h := Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt (C.erase j)
    (by
      intro j' h0 h1 hj'
      by_cases e : j' = j
      · subst e; exact hadj
      · exact hex j' h0 h1 (fun h => hj' (Finset.mem_erase.2 ⟨e, h⟩)))
  rw [Finset.card_erase_of_mem hj] at h
  have := Finset.card_pos.2 ⟨j, hj⟩
  omega
-- <</B20.head_forced>>

-- <<B20.last_deg_le>>
lemma Cadre.last_deg_le [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (C : Finset ℕ)
    (hex : ∀ j, j + 1 < l.length → j ∉ C →
      ¬ G.Adj (l.getD j x₀) (l.getD (l.length - 1) x₀)) :
    G.degree (l.getD (l.length - 1) x₀) ≤ C.card := by
  have hmx := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have h2 := b15_len2 hne hmem hhd
  obtain ⟨-, -, -, -, -, h5⟩ := lemma4x hconn l hne hnd hch hmx hlt h2
  have e := b15_last hne x₀
  rw [← e]
  refine h5.trans (Finset.card_le_card ?_)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  by_contra hC'
  apply hex j (by omega) hC'
  have := hj.2
  rwa [e, b15_dflt (l := l) (i := j) (by omega) (l.head hne) x₀] at this
-- <</B20.last_deg_le>>

-- <<B20.last_forced>>
lemma Cadre.last_forced [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (C : Finset ℕ) (hCr : ∀ j ∈ C, j + 1 < l.length)
    (hex : ∀ j, j + 1 < l.length → j ∉ C →
      ¬ G.Adj (l.getD j x₀) (l.getD (l.length - 1) x₀))
    (hdeg : C.card ≤ G.degree (l.getD (l.length - 1) x₀)) :
    ∀ j ∈ C, G.Adj (l.getD j x₀) (l.getD (l.length - 1) x₀) := by
  intro j hj
  by_contra hadj
  have h := Cadre.last_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt (C.erase j)
    (by
      intro j' h1 hj'
      by_cases e : j' = j
      · subst e; exact hadj
      · exact hex j' h1 (fun h => hj' (Finset.mem_erase.2 ⟨e, h⟩)))
  rw [Finset.card_erase_of_mem hj] at h
  have := Finset.card_pos.2 ⟨j, hj⟩
  omega
-- <</B20.last_forced>>


-- <<B22.C1>>

lemma b22_E [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w)
    (huw : u ≠ w) (h1 : G.Adj u v) (h2 : G.Adj v w)
    (a j : ℕ) (hA : G.Adj w (l.getD a x₀)) (haj : a < j) (hj : j < l.length) (hja : j ≤ a + 3)
    (hx : ∃ i, (i ≤ a ∨ j ≤ i) ∧ i < l.length ∧ l.getD i x₀ = x₀) :
    ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀) := by
  intro h
  have hs : [u, v, w] ≠ [] := by simp
  have snd : [u, v, w].Nodup := by simp [huv, hvw, huw]
  have sch : [u, v, w].IsChain G.Adj := by simp [List.isChain_cons_cons, h1, h2]
  have sl : ∀ x ∈ [u, v, w], x ∉ l := by
    intro x hx'
    have : x ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simpa using hx'
    simpa using this
  exact Cadre.endE hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [u, v, w] hs snd sch sl a j haj hj h (by simpa using hA) hx
    (by simp; omega)

lemma b22_gam [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y : V) (hy : y ∉ l) (P : Finset ℕ)
    (hP : ∀ a ∈ P, 2 ≤ a ∧ a + 1 < l.length ∧ G.Adj y (l.getD a x₀)) :
    ∀ a ∈ P, secondSmallestDegree G < (P.image (· + 1) ∪ P.image (· - 1)).card + 1 →
      ¬ G.Adj (l.getD 0 x₀) (l.getD a x₀) := by
  intro a ha hcard h
  have hl0 : 0 < l.length := List.length_pos_iff.mpr hne
  have hn0 : ¬ G.Adj y (l.getD 0 x₀) := by
    intro hh
    have := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy (j := 0)
      (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hl0, hh⟩)
    omega
  set I : Finset ℕ := insert 0 (P.image (· + 1) ∪ P.image (· - 1)) with hI
  have hmemD : ∀ i ∈ P.image (· + 1) ∪ P.image (· - 1), i < l.length ∧ G.dist y (l.getD i x₀) = 2 := by
    intro i hi
    refine Cadre.dset_dist hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy ?_
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a',
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hP a' ha'; omega), (hP a' ha').2.2⟩, rfl⟩)
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a',
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hP a' ha'; omega), (hP a' ha').2.2⟩, rfl⟩)
  have hmemI : ∀ i ∈ I, i < l.length ∧ G.dist y (l.getD i x₀) = 2 := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · refine ⟨hl0, dist_two hconn (a := l.getD a x₀) (hP a ha).2.2 h.symm hn0 ?_⟩
      intro e
      exact hy (by rw [← e]; exact List.getD_eq_getElem _ _ hl0 ▸ List.getElem_mem _)
    · exact hmemD i hi
  have h0 : (0 : ℕ) ∉ P.image (· + 1) ∪ P.image (· - 1) := by
    intro h0
    rcases Finset.mem_union.mp h0 with h0 | h0
    · obtain ⟨a', ha', e⟩ := Finset.mem_image.mp h0; omega
    · obtain ⟨a', ha', e⟩ := Finset.mem_image.mp h0
      have := (hP a' ha').1; omega
  have hcardI : I.card = (P.image (· + 1) ∪ P.image (· - 1)).card + 1 := by
    rw [hI, Finset.card_insert_of_notMem h0]
  have hinj : Set.InjOn (fun i => l.getD i x₀) (I : Set ℕ) := by
    intro i hi i' hi' he
    have e1 := (hmemI i hi).1
    have e2 := (hmemI i' hi').1
    simp only at he
    rw [List.getD_eq_getElem _ _ e1, List.getD_eq_getElem _ _ e2] at he
    exact (List.Nodup.getElem_inj_iff hnd).mp he
  have hle := card_le_gamma hconn hH y (I.image (fun i => l.getD i x₀)) (by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact (hmemI i hi).2)
  rw [Finset.card_image_of_injOn hinj, hcardI] at hle
  omega

lemma b22_h0 {l : List V} {x₀ : V} (hne : l ≠ []) (hhd : l.head hne ≠ x₀) : l.getD 0 x₀ ≠ x₀ := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => simpa using hhd


lemma Cadre.C1 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 10)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 6 x₀))
    (hx : l.getD 1 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {2, 6} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 1 ∧ l.getD i0 x₀ = x₀ := ⟨1, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 10 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact hGa 2 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 3 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 6 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 7 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1} : Finset ℕ).card < 4 := by decide
  omega
-- <</B22.C1>>

-- <<B22.C3>>
lemma Cadre.C3 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 11)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 6 x₀))
    (hx : l.getD 1 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {2, 6} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 1 ∧ l.getD i0 x₀ = x₀ := ⟨1, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 10} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 10} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 11 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact hGa 2 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 3 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 6 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 7 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact absurd (by simp) hjC
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 10} : Finset ℕ).card < 4 := by decide
  omega
-- <</B22.C3>>

-- <<B22.C4>>
lemma Cadre.C4 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 11)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 7 x₀))
    (hx : l.getD 1 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {2, 7} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 1 ∧ l.getD i0 x₀ = x₀ := ⟨1, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 6} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 6} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 11 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact hGa 2 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 3 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact absurd (by simp) hjC
    · exact hGa 7 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 10 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 6} : Finset ℕ).card < 4 := by decide
  omega
-- <</B22.C4>>

-- <<B22.C5>>
lemma Cadre.C5 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 11)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 3 x₀) ∧ G.Adj y (l.getD 7 x₀))
    (hx : l.getD 1 x₀ = x₀ ∨ l.getD 2 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {3, 7} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, (1 ≤ i0 ∧ i0 ≤ 2) ∧ l.getD i0 x₀ = x₀ := by rcases hx with h | h; exact ⟨1, by omega, h⟩; exact ⟨2, by omega, h⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 2} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 2} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 11 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact absurd (by simp) hjC
    · exact hGa 3 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 6 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 7 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 10 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 2} : Finset ℕ).card < 4 := by decide
  omega
-- <</B22.C5>>

-- <<B22.C9>>
lemma Cadre.C9 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 11)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 3 x₀) ∧ G.Adj y (l.getD 7 x₀))
    (hx : l.getD 5 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {3, 7} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 5 ∧ l.getD i0 x₀ = x₀ := ⟨5, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 2, 6} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 2, 6} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 11 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact absurd (by simp) hjC
    · exact hGa 3 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact absurd (by simp) hjC
    · exact hGa 7 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 10 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 2, 6} : Finset ℕ).card < 4 := by decide
  omega
-- <</B22.C9>>

-- <<B22.C10>>
lemma Cadre.C10 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 5) (hm : l.length = 13)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 3 x₀) ∧ G.Adj y (l.getD 7 x₀) ∧ G.Adj y (l.getD 9 x₀))
    (hx : l.getD 8 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {3, 7, 9} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2.1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2.2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 8 ∧ l.getD i0 x₀ = x₀ := ⟨8, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 2} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 2} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 13 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact absurd (by simp) hjC
    · exact hGa 3 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 6 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 7 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 8 (hA w (by simp)).2.1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 9 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 9 10 (hA w (by simp)).2.2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 9 11 (hA w (by simp)).2.2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 9 12 (hA w (by simp)).2.2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 2} : Finset ℕ).card < 5 := by decide
  omega
-- <</B22.C10>>
-- <<B21>>
lemma b21_clq {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) :
    ∀ a ∈ ({u, v, w} : Finset V), ∀ b ∈ ({u, v, w} : Finset V), a ≠ b → G.Adj a b := by
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | assumption | exact (G.adj_comm _ _).1 (by assumption)

lemma b21_path {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) {y1 y2 : V}
    (hy1 : y1 ∈ ({u, v, w} : Finset V)) (hy2 : y2 ∈ ({u, v, w} : Finset V)) (hne : y1 ≠ y2) :
    ∃ s : List V, ∃ hs : s ≠ [], s.Nodup ∧ s.IsChain G.Adj ∧ (∀ x ∈ s, x ∈ ({u, v, w} : Finset V)) ∧
      s.length = 3 ∧ s.head hs = y1 ∧ s.getLast hs = y2 := by
  have hc := b21_clq huv hvw huw h1 h2 h3
  have hcard : ({u, v, w} : Finset V).card = 3 := Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  have hlt : ({y1, y2} : Finset V).card < ({u, v, w} : Finset V).card := by
    rw [hcard, Finset.card_pair hne]; omega
  obtain ⟨z, hz, hz'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz'
  refine ⟨[y1, z, y2], by simp, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [hne, Ne.symm hz'.1, hz'.2]
  · simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
    exact ⟨hc y1 hy1 z hz (Ne.symm hz'.1), hc z hz y2 hy2 hz'.2⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

lemma b21_rdeg [DecidableRel G.Adj] {l : List V} {u v w : V} (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w})
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) {y : V} (hy : y ∈ ({u, v, w} : Finset V)) :
    (((Finset.univ.filter (fun t => t ∉ l))).filter (G.Adj y)).card = 2 := by
  have hc := b21_clq huv hvw huw h1 h2 h3
  have hcard : ({u, v, w} : Finset V).card = 3 := Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  rw [hR]
  have : ({u, v, w} : Finset V).filter (G.Adj y) = ({u, v, w} : Finset V).erase y := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hz, h⟩; exact ⟨(G.ne_of_adj h).symm, hz⟩
    · rintro ⟨hne, hz⟩; exact ⟨hz, hc y hy z hz (Ne.symm hne)⟩
  rw [this, Finset.card_erase_of_mem hy, hcard]

lemma b21_mem {l : List V} {u v w : V} (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) {y : V} :
    y ∈ ({u, v, w} : Finset V) ↔ y ∉ l := by
  rw [← hR]; simp

lemma b21_getD_mem {l : List V} {d : V} {i : ℕ} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

lemma b21_inj {l : List V} (hnd : l.Nodup) {d : V} {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : l.getD i d = l.getD j d) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (hnd.getElem_inj_iff).mp h

lemma b21_Dcard (J : Finset ℕ) (hJ : J.Nonempty) (hb : ∀ j ∈ J, 0 < j) :
    J.card + 1 ≤ (J.image (· + 1) ∪ J.image (· - 1)).card := by
  have hm0 := Finset.min'_mem J hJ
  have hpos := hb _ hm0
  have hnot : J.min' hJ - 1 ∉ J.image (· + 1) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro j hj hjm
    have := Finset.min'_le J j hj
    omega
  have hsub : insert (J.min' hJ - 1) (J.image (· + 1)) ⊆ J.image (· + 1) ∪ J.image (· - 1) := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hm0, rfl⟩)
    · exact Finset.mem_union_left _ hx
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ (add_left_injective 1)] at this
  exact this

lemma b21_a [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (A : Finset ℕ)
    (hA : ∀ i, i ∈ A ↔ i < l.length ∧ ∃ z ∈ ({u, v, w} : Finset V), G.Adj z (l.getD i x₀)) :
    (∀ a ∈ A, 1 ≤ a ∧ a + 2 ≤ l.length) ∧ 2 ≤ A.card ∧ A.card + 1 ≤ secondSmallestDegree G ∧
    secondSmallestDegree G ≤ A.card + 2 ∧
    (∀ y ∈ ({u, v, w} : Finset V), ∃ a ∈ A, G.Adj y (l.getD a x₀)) ∧
    (∀ y ∈ ({u, v, w} : Finset V), secondSmallestDegree G = A.card + 2 → ∀ a ∈ A, G.Adj y (l.getD a x₀)) ∧
    (∀ y ∈ ({u, v, w} : Finset V), (A.filter (fun i => ¬ G.Adj y (l.getD i x₀))).card ≤ 1) := by
  have hc := b21_clq huv hvw huw h1 h2 h3
  have hRl : ∀ y ∈ ({u, v, w} : Finset V), y ∉ l := fun y hy => (b21_mem hR).1 hy
  have hJ : ∀ y ∈ ({u, v, w} : Finset V), A.filter (fun i => G.Adj y (l.getD i x₀)) =
      (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := by
    intro y hy
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, hA]
    constructor
    · rintro ⟨⟨hi, _⟩, h⟩; exact ⟨hi, h⟩
    · rintro ⟨hi, h⟩; exact ⟨⟨hi, y, hy, h⟩, h⟩
  have hdeg : ∀ y ∈ ({u, v, w} : Finset V), G.degree y = (A.filter (fun i => G.Adj y (l.getD i x₀))).card + 2 := by
    intro y hy
    rw [hJ y hy, Cadre.degree_split hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt (hRl y hy), b21_rdeg hR huv hvw huw h1 h2 h3 hy]
  have hxl : ∀ y ∈ ({u, v, w} : Finset V), y ≠ x₀ := fun y hy h => hRl y hy (h ▸ hmem)
  have hS1 : ∀ a ∈ A, 1 ≤ a ∧ a + 2 ≤ l.length := by
    intro a ha
    obtain ⟨hal, z, hz, hza⟩ := (hA a).1 ha
    have := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt (hRl z hz) (j := a) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hal, hza⟩)
    omega
  have hS2 : 2 ≤ A.card := by
    obtain ⟨a, b, hab, hbl, ⟨y1, hy1, hy1a⟩, ⟨y2, hy2, hy2b⟩⟩ := Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    rw [hR] at hy1 hy2
    have ha : a ∈ A := (hA a).2 ⟨by omega, y1, hy1, hy1a⟩
    have hb' : b ∈ A := (hA b).2 ⟨hbl, y2, hy2, hy2b⟩
    exact Finset.one_lt_card.mpr ⟨a, ha, b, hb', by omega⟩
  have hS3 : A.card + 1 ≤ secondSmallestDegree G := by
    obtain ⟨a, b, hab, hbl, ⟨y1, hy1, hy1a⟩, _⟩ := Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    rw [hR] at hy1
    have hnonempty : ((Finset.range l.length).filter (fun i => G.Adj y1 (l.getD i x₀))).Nonempty :=
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hy1a⟩⟩
    have hbp := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y1 (hRl y1 hy1)
      ((A.filter (fun i => ¬ G.Adj y1 (l.getD i x₀))).image (fun i => l.getD i x₀)) ∅
      (by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter] at hx
        obtain ⟨i, ⟨hiA, hni⟩, rfl⟩ := hx
        obtain ⟨hil, z, hz, hza⟩ := (hA i).1 hiA
        have hzy : z ≠ y1 := fun h => hni (h ▸ hza)
        exact ⟨b21_getD_mem hil, hni, z, hRl z hz, hc y1 hy1 z hz (Ne.symm hzy), hza⟩)
      (by simp)
    have hDc := b21_Dcard _ hnonempty (fun j hj => (Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt (hRl y1 hy1) hj).1)
    have himg : ((A.filter (fun i => ¬ G.Adj y1 (l.getD i x₀))).image (fun i => l.getD i x₀)).card =
        (A.filter (fun i => ¬ G.Adj y1 (l.getD i x₀))).card := by
      apply Finset.card_image_of_injOn
      intro i hi j hj hij
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi hj
      exact b21_inj hnd ((hA i).1 hi.1).1 ((hA j).1 hj.1).1 hij
    have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun i => G.Adj y1 (l.getD i x₀))
    rw [hJ y1 hy1] at hsplit
    simp only [Finset.card_empty] at hbp
    omega
  have hS4 : secondSmallestDegree G ≤ A.card + 2 := by
    have := hx0 u (hxl u (by simp)) 
    rw [hdeg u (by simp)] at this
    have := Finset.card_filter_le A (fun i => G.Adj u (l.getD i x₀))
    omega
  have hS5 : ∀ y ∈ ({u, v, w} : Finset V), ∃ a ∈ A, G.Adj y (l.getD a x₀) := by
    intro y hy
    have h := hx0 y (hxl y hy)
    rw [hdeg y hy] at h
    have : 0 < (A.filter (fun i => G.Adj y (l.getD i x₀))).card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp this
    rw [Finset.mem_filter] at ha
    exact ⟨a, ha.1, ha.2⟩
  have hS6 : ∀ y ∈ ({u, v, w} : Finset V), secondSmallestDegree G = A.card + 2 → ∀ a ∈ A, G.Adj y (l.getD a x₀) := by
    intro y hy hσ a ha
    have h := hx0 y (hxl y hy)
    rw [hdeg y hy] at h
    have := Finset.eq_of_subset_of_card_le (Finset.filter_subset (fun i => G.Adj y (l.getD i x₀)) A) (by omega)
    rw [← this] at ha
    exact (Finset.mem_filter.mp ha).2
  have hS7 : ∀ y ∈ ({u, v, w} : Finset V), (A.filter (fun i => ¬ G.Adj y (l.getD i x₀))).card ≤ 1 := by
    intro y hy
    have h := hx0 y (hxl y hy)
    rw [hdeg y hy] at h
    have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun i => G.Adj y (l.getD i x₀))
    omega
  exact ⟨hS1, hS2, hS3, hS4, hS5, hS6, hS7⟩

lemma b21_other {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) (y : V) :
    ∃ y' ∈ ({u, v, w} : Finset V), y' ≠ y := by
  have hcard : ({u, v, w} : Finset V).card = 3 := Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  exact Finset.exists_mem_ne (by omega) y

lemma b21_c [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (A : Finset ℕ)
    (hA : ∀ i, i ∈ A ↔ i < l.length ∧ ∃ z ∈ ({u, v, w} : Finset V), G.Adj z (l.getD i x₀))
    (i₀ : ℕ) (hi₀ : i₀ < l.length ∧ l.getD i₀ x₀ = x₀)
    (hS2 : 2 ≤ A.card)
    (hS7 : ∀ y ∈ ({u, v, w} : Finset V), (A.filter (fun i => ¬ G.Adj y (l.getD i x₀))).card ≤ 1) :
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ y1 ∈ ({u, v, w} : Finset V), ∃ y2 ∈ ({u, v, w} : Finset V),
      y1 ≠ y2 ∧ G.Adj y1 (l.getD a x₀) ∧ G.Adj y2 (l.getD b x₀)) ∧
    (∀ a ∈ A, 3 ≤ a ∨ i₀ < a) ∧ (∀ a ∈ A, a + 4 ≤ l.length ∨ a < i₀) ∧
    (∀ a ∈ A, ∀ b ∈ A, a < b → a + 2 ≤ b ∧ (a + 4 ≤ b ∨ (a < i₀ ∧ i₀ < b))) := by
  have hRl : ∀ y ∈ ({u, v, w} : Finset V), y ∉ l := fun y hy => (b21_mem hR).1 hy
  have huniq : ∀ i, i < l.length → l.getD i x₀ = x₀ → i = i₀ :=
    fun i hi h => b21_inj hnd hi hi₀.1 (h.trans hi₀.2.symm)
  have hcross : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ y1 ∈ ({u, v, w} : Finset V), ∃ y2 ∈ ({u, v, w} : Finset V),
      y1 ≠ y2 ∧ G.Adj y1 (l.getD a x₀) ∧ G.Adj y2 (l.getD b x₀) := by
    intro a ha b hb hab
    by_contra hno
    push Not at hno
    obtain ⟨_, y1, hy1, hy1a⟩ := (hA a).1 ha
    obtain ⟨_, y2, hy2, hy2b⟩ := (hA b).1 hb
    have hyy : y1 = y2 := by
      by_contra hne'
      exact hno y1 hy1 y2 hy2 hne' hy1a hy2b
    subst hyy
    obtain ⟨v', hv', hvy⟩ := b21_other huv hvw huw y1
    have hva : ¬ G.Adj v' (l.getD a x₀) := fun h => hno v' hv' y1 hy1 hvy h hy2b
    have hvb : ¬ G.Adj v' (l.getD b x₀) := fun h => hno y1 hy1 v' hv' (Ne.symm hvy) hy1a h
    have hsub : ({a, b} : Finset ℕ) ⊆ A.filter (fun i => ¬ G.Adj v' (l.getD i x₀)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨ha, hva⟩
      · exact Finset.mem_filter.mpr ⟨hb, hvb⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hab] at this
    have := hS7 v' hv'
    omega
  have hL : ∀ a ∈ A, 3 ≤ a ∨ i₀ < a := by
    intro a ha
    by_contra hcon
    push Not at hcon
    obtain ⟨hal, z, hz, hza⟩ := (hA a).1 ha
    obtain ⟨y', hy', hyz⟩ := b21_other huv hvw huw z
    obtain ⟨s, hs, snd, sch, hsR, hlen, -, hlast'⟩ := b21_path huv hvw huw h1 h2 h3 hy' hz hyz
    refine Cadre.no_pre hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch (fun x hx => hRl x (hsR x hx)) a hal ?_ ?_ (by omega)
    · rw [hlast']; exact hza
    · intro i hi heq
      have := huniq i (by omega) heq
      omega
  have hRt : ∀ a ∈ A, a + 4 ≤ l.length ∨ a < i₀ := by
    intro a ha
    by_contra hcon
    push Not at hcon
    obtain ⟨hal, z, hz, hza⟩ := (hA a).1 ha
    obtain ⟨y', hy', hyz⟩ := b21_other huv hvw huw z
    obtain ⟨s, hs, snd, sch, hsR, hlen, hhead, -⟩ := b21_path huv hvw huw h1 h2 h3 hz hy' (Ne.symm hyz)
    refine Cadre.no_suf hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch (fun x hx => hRl x (hsR x hx)) a hal ?_ ?_ (by omega)
    · rw [hhead]; exact (G.adj_comm _ _).1 hza
    · intro i hi hil heq
      have := huniq i hil heq
      omega
  have hM : ∀ a ∈ A, ∀ b ∈ A, a < b → a + 2 ≤ b ∧ (a + 4 ≤ b ∨ (a < i₀ ∧ i₀ < b)) := by
    intro a ha b hbA hab
    have hdis : a + 4 ≤ b ∨ (a < i₀ ∧ i₀ < b) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hal, _⟩ := (hA a).1 ha
      obtain ⟨hbl, _⟩ := (hA b).1 hbA
      obtain ⟨y1, hy1, y2, hy2, hy12, hy1a, hy2b⟩ := hcross a ha b hbA (by omega)
      obtain ⟨s, hs, snd, sch, hsR, hlen, hhead, hlast'⟩ := b21_path huv hvw huw h1 h2 h3 hy1 hy2 hy12
      refine Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch (fun x hx => hRl x (hsR x hx)) a b hab hbl ?_ ?_ ?_ (by omega)
      · rw [hhead]; exact (G.adj_comm _ _).1 hy1a
      · rw [hlast']; exact hy2b
      · intro i hi1 hi2 heq
        have := huniq i (by omega) heq
        have := hcon.2
        omega
    refine ⟨?_, hdis⟩
    omega
  exact ⟨hcross, hL, hRt, hM⟩

lemma b21_pack (A : Finset ℕ) {m i₀ : ℕ} (hS2 : 2 ≤ A.card)
    (hS1 : ∀ a ∈ A, 1 ≤ a ∧ a + 2 ≤ m) (hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ m)
    (hL : ∀ a ∈ A, 3 ≤ a ∨ i₀ < a) (hRt : ∀ a ∈ A, a + 4 ≤ m ∨ a < i₀)
    (hM : ∀ a ∈ A, ∀ b ∈ A, a < b → a + 2 ≤ b ∧ (a + 4 ≤ b ∨ (a < i₀ ∧ i₀ < b))) :
    4 * A.card + 1 ≤ m := by
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have := pack A ∅ m 3 i₀ (by norm_num) hAne (Finset.empty_subset _) hS1 hi
    (by have := hL _ (Finset.min'_mem A hAne); omega)
    (by have := hRt _ (Finset.max'_mem A hAne); omega)
    (by
      intro a ha b hb hab _
      have := hM a ha b hb hab
      refine ⟨this.1, fun _ => ?_⟩
      omega)
  simpa using this

set_option maxHeartbeats 2000000 in
lemma b21_core [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (P Q i₀ : ℕ) (hs : (secondSmallestDegree G = 3 ∧ l.length = 9) ∨ (secondSmallestDegree G = 4 ∧ l.length = 10) ∨
      (secondSmallestDegree G = 4 ∧ l.length = 11))
    (h1P : 1 ≤ P) (hQ : Q + 2 ≤ l.length) (hPQ : P < Q) (hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ l.length)
    (hLP : 3 ≤ P ∨ i₀ < P) (hLQ : 3 ≤ Q ∨ i₀ < Q) (hRP : P + 4 ≤ l.length ∨ P < i₀)
    (hRQ : Q + 4 ≤ l.length ∨ Q < i₀) (hM : P + 2 ≤ Q ∧ (P + 4 ≤ Q ∨ (P < i₀ ∧ i₀ < Q)))
    (hi₀ : l.getD i₀ x₀ = x₀)
    (hAny : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD P x₀) ∨ G.Adj y (l.getD Q x₀))
    (hAll : 4 ≤ secondSmallestDegree G → ∀ y ∈ ({u, v, w} : Finset V),
      G.Adj y (l.getD P x₀) ∧ G.Adj y (l.getD Q x₀))
    (hcr : ∃ y1 ∈ ({u, v, w} : Finset V), ∃ y2 ∈ ({u, v, w} : Finset V),
      y1 ≠ y2 ∧ G.Adj y1 (l.getD P x₀) ∧ G.Adj y2 (l.getD Q x₀))
    (hcore : i₀ ≤ P + 1 ∨ i₀ = Q ∨ (i₀ = P + 2 ∧ Q = P + 4)) : False := by
  have hRl : ∀ y ∈ ({u, v, w} : Finset V), y ∉ l := fun y hy => (b21_mem hR).1 hy
  have hcard : ({u, v, w} : Finset V).card = 3 := Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  have hB17 : secondSmallestDegree G ≤ 4 → Q = P + 2 → i₀ = P + 1 → False := by
    intro hs4 hQ2 hi
    subst hQ2 hi
    obtain ⟨y1, hy1, y2, hy2, hy12, hy1a, hy2b⟩ := hcr
    obtain ⟨s, hs, snd, sch, hsR, hlen, hhead, hlast'⟩ := b21_path huv hvw huw h1 h2 h3 hy1 hy2 hy12
    have := Cadre.hole_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt ({u, v, w} : Finset V) hRl P h1P (by omega) hi₀ hAny s hs snd sch
      (fun x hx => hRl x (hsR x hx)) (by rw [hhead]; exact (G.adj_comm _ _).1 hy1a)
      (by rw [hlast']; exact hy2b)
    omega
  have hB18 : secondSmallestDegree G = 4 → (i₀ = P ∨ i₀ = Q) → False := by
    intro hs4 hi
    have := Cadre.x0_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt ({u, v, w} : Finset V) hRl i₀ (by omega) (by omega) hi₀
      (by
        intro y hy
        have := hAll (by omega) y hy
        rcases hi with rfl | rfl
        · rw [← hi₀]; exact this.1
        · rw [← hi₀]; exact this.2)
    omega
  have hB19 : secondSmallestDegree G = 4 → i₀ = P + 1 → P + 3 ≤ Q → Q ≤ P + 4 → False := by
    intro hs4 hi hq1 hq2
    subst hi
    obtain ⟨s, hs, snd, sch, hsR, hlen, -, -⟩ := b21_path huv hvw huw h1 h2 h3
      (y1 := u) (y2 := v) (by simp) (by simp) huv
    exact Cadre.walk_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch (fun x hx => hRl x (hsR x hx)) P Q h1P hq1 (by omega) hi₀
      (fun y hy => (hAll (by omega) y (hsR y hy)).1) (fun y hy => (hAll (by omega) y (hsR y hy)).2)
      (by omega) (by omega)
  rcases hcore with hc | hc | hc
  · rcases lt_or_ge i₀ P with hlt' | hge
    · rcases hs with ⟨hσ, hm⟩ | ⟨hσ, hm⟩ | ⟨hσ, hm⟩
      · omega
      · have e : P = 2 ∧ Q = 6 ∧ i₀ = 1 := by omega
        obtain ⟨rfl, rfl, rfl⟩ := e
        exact Cadre.C1 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy) hi₀
      · have e : (P = 2 ∧ Q = 6 ∧ i₀ = 1) ∨ (P = 2 ∧ Q = 7 ∧ i₀ = 1) ∨ (P = 3 ∧ Q = 7 ∧ (i₀ = 1 ∨ i₀ = 2)) := by
          omega
        rcases e with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hi12⟩
        · exact Cadre.C3 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy) hi₀
        · exact Cadre.C4 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy) hi₀
        · exact Cadre.C5 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy)
            (by rcases hi12 with rfl | rfl; exacts [Or.inl hi₀, Or.inr hi₀])
    · have hσ4 : secondSmallestDegree G ≤ 4 := by omega
      rcases (by omega : i₀ = P ∨ (i₀ = P + 1 ∧ Q = P + 2) ∨ (i₀ = P + 1 ∧ P + 3 ≤ Q)) with he | ⟨he, hq⟩ | ⟨he, hq⟩
      · exact hB18 (by omega) (Or.inl he)
      · exact hB17 hσ4 hq he
      · exact hB19 (by omega) he hq (by omega)
  · exact hB18 (by omega) (Or.inr hc)
  · obtain ⟨hi2, hq⟩ := hc
    have hσ : secondSmallestDegree G = 4 := by omega
    have hm : l.length = 11 := by omega
    have e : P = 3 ∧ Q = 7 ∧ i₀ = 5 := by omega
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact Cadre.C9 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy) hi₀

set_option maxHeartbeats 2000000 in
lemma b21_fin2 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (P Q i₀ : ℕ) (hs : (secondSmallestDegree G = 3 ∧ l.length = 9) ∨ (secondSmallestDegree G = 4 ∧ l.length = 10) ∨
      (secondSmallestDegree G = 4 ∧ l.length = 11))
    (h1P : 1 ≤ P) (hQ : Q + 2 ≤ l.length) (hPQ : P < Q) (hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ l.length)
    (hLP : 3 ≤ P ∨ i₀ < P) (hLQ : 3 ≤ Q ∨ i₀ < Q) (hRP : P + 4 ≤ l.length ∨ P < i₀)
    (hRQ : Q + 4 ≤ l.length ∨ Q < i₀) (hM : P + 2 ≤ Q ∧ (P + 4 ≤ Q ∨ (P < i₀ ∧ i₀ < Q)))
    (hi₀ : l.getD i₀ x₀ = x₀)
    (hAny : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD P x₀) ∨ G.Adj y (l.getD Q x₀))
    (hAll : 4 ≤ secondSmallestDegree G → ∀ y ∈ ({u, v, w} : Finset V),
      G.Adj y (l.getD P x₀) ∧ G.Adj y (l.getD Q x₀))
    (hcr : ∃ y1 ∈ ({u, v, w} : Finset V), ∃ y2 ∈ ({u, v, w} : Finset V),
      y1 ≠ y2 ∧ G.Adj y1 (l.getD P x₀) ∧ G.Adj y2 (l.getD Q x₀)) : False := by
  by_cases hcore : i₀ ≤ P + 1 ∨ i₀ = Q ∨ (i₀ = P + 2 ∧ Q = P + 4)
  · exact b21_core hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 P Q i₀ hs h1P hQ hPQ hi hLP hLQ hRP hRQ hM hi₀ hAny hAll hcr hcore
  · obtain ⟨hne', hnd', hch', hmem', hhd', hlast', hmax', hlt'⟩ := Cadre.reverse hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hR' : (Finset.univ.filter (fun t => t ∉ l.reverse)) = {u, v, w} := by
      simpa [List.mem_reverse] using hR
    have hrev : ∀ j, j < l.length → l.reverse.getD (l.length - 1 - j) x₀ = l.getD j x₀ := by
      intro j hj
      rw [Cadre.getD_reverse l x₀ (by omega)]
      have : l.length - 1 - (l.length - 1 - j) = j := by omega
      rw [this]
    refine b21_core (l := l.reverse) hconn hb hH hmin hx0 hδ hne' hnd' hch' hmem' hhd' hlast' hmax' hlt'
      u v w hR' huv hvw huw h1 h2 h3 (l.length - 1 - Q) (l.length - 1 - P) (l.length - 1 - i₀)
      (by rw [List.length_reverse]; exact hs)
      (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega)
      (by rw [hrev i₀ (by omega)]; exact hi₀)
      (fun y hy => by rw [hrev Q (by omega), hrev P (by omega)]; exact (hAny y hy).symm)
      (fun h y hy => by
        rw [hrev Q (by omega), hrev P (by omega)]
        exact ⟨(hAll h y hy).2, (hAll h y hy).1⟩)
      (by
        obtain ⟨y1, hy1, y2, hy2, hne2, ha, hb2⟩ := hcr
        exact ⟨y2, hy2, y1, hy1, Ne.symm hne2, by rw [hrev Q (by omega)]; exact hb2,
          by rw [hrev P (by omega)]; exact ha⟩)
      (by (try simp only [List.length_reverse]); omega)

lemma b21_fin3r [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (hσ : secondSmallestDegree G = 5) (hm : l.length = 13)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 3 x₀) ∧ G.Adj y (l.getD 5 x₀) ∧ G.Adj y (l.getD 9 x₀))
    (hx : l.getD 4 x₀ = x₀) : False := by
  obtain ⟨hne', hnd', hch', hmem', hhd', hlast', hmax', hlt'⟩ := Cadre.reverse hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hR' : (Finset.univ.filter (fun t => t ∉ l.reverse)) = {u, v, w} := by
    simpa [List.mem_reverse] using hR
  have hrev : ∀ j, j < l.length → l.reverse.getD (l.length - 1 - j) x₀ = l.getD j x₀ := by
    intro j hj
    rw [Cadre.getD_reverse l x₀ (by omega)]
    have : l.length - 1 - (l.length - 1 - j) = j := by omega
    rw [this]
  have e3 : l.reverse.getD 3 x₀ = l.getD 9 x₀ := by
    have := hrev 9 (by omega); rwa [show l.length - 1 - 9 = 3 by omega] at this
  have e7 : l.reverse.getD 7 x₀ = l.getD 5 x₀ := by
    have := hrev 5 (by omega); rwa [show l.length - 1 - 5 = 7 by omega] at this
  have e9 : l.reverse.getD 9 x₀ = l.getD 3 x₀ := by
    have := hrev 3 (by omega); rwa [show l.length - 1 - 3 = 9 by omega] at this
  have e8 : l.reverse.getD 8 x₀ = l.getD 4 x₀ := by
    have := hrev 4 (by omega); rwa [show l.length - 1 - 4 = 8 by omega] at this
  exact Cadre.C10 (l := l.reverse) hconn hb hH hmin hx0 hδ hne' hnd' hch' hmem' hhd' hlast' hmax' hlt'
    hσ (by rw [List.length_reverse]; exact hm) u v w hR' huv hvw huw h1 h2 h3
    (fun y hy => by
      rw [e3, e7, e9]
      exact ⟨(hA y hy).2.2, (hA y hy).2.1, (hA y hy).1⟩)
    (by rw [e8]; exact hx)

set_option maxHeartbeats 4000000 in
lemma Cadre.K3 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hm : l.length = 2 * secondSmallestDegree G + 2 ∨ l.length = 2 * secondSmallestDegree G + 3) :
    False := by
  have hRl : ∀ y ∈ ({u, v, w} : Finset V), y ∉ l := fun y hy => (b21_mem hR).1 hy
  obtain ⟨i₀, hi₀l, hi₀⟩ : ∃ i, i < l.length ∧ l.getD i x₀ = x₀ := by
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hmem
    exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact he⟩
  have hi₀b : 1 ≤ i₀ ∧ i₀ + 2 ≤ l.length := by
    have hpos := List.length_pos_of_ne_nil hne
    have h0 : l.head hne = l.getD 0 x₀ := by
      cases l with
      | nil => exact absurd rfl hne
      | cons a t => simp
    have hL' : l.getLast hne = l.getD (l.length - 1) x₀ := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
    constructor
    · by_contra h
      have : i₀ = 0 := by omega
      subst this
      exact hhd (h0.trans hi₀)
    · by_contra h
      have : i₀ = l.length - 1 := by omega
      subst this
      exact hlast (hL'.trans hi₀)
  obtain ⟨A, hAdef⟩ : ∃ A : Finset ℕ, A = (Finset.range l.length).filter
      (fun i => ∃ z ∈ ({u, v, w} : Finset V), G.Adj z (l.getD i x₀)) := ⟨_, rfl⟩
  have hA : ∀ i, i ∈ A ↔ i < l.length ∧ ∃ z ∈ ({u, v, w} : Finset V), G.Adj z (l.getD i x₀) := by
    intro i; rw [hAdef, Finset.mem_filter, Finset.mem_range]
  obtain ⟨hS1, hS2, hS3, hS4, hS5, hS6, hS7⟩ := b21_a hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 A hA
  obtain ⟨hcross, hL, hRt, hM⟩ := b21_c hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 A hA i₀ ⟨hi₀l, hi₀⟩ hS2 hS7
  have hpk := b21_pack A hS2 hS1 hi₀b hL hRt hM
  have hr : A.card = 2 ∨ A.card = 3 := by omega
  rcases hr with hr | hr
  · obtain ⟨a, b, hab, hAab⟩ := Finset.card_eq_two.mp hr
    have key : ∀ P Q, P < Q → A = {P, Q} → False := by
      intro P Q hPQ hAPQ
      have hPA : P ∈ A := by rw [hAPQ]; simp
      have hQA : Q ∈ A := by rw [hAPQ]; simp
      have h1P := hS1 P hPA
      have h1Q := hS1 Q hQA
      have hLP := hL P hPA
      have hLQ := hL Q hQA
      have hRP := hRt P hPA
      have hRQ := hRt Q hQA
      have hMPQ := hM P hPA Q hQA hPQ
      have hAny : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD P x₀) ∨ G.Adj y (l.getD Q x₀) := by
        intro y hy
        obtain ⟨a', ha', hya⟩ := hS5 y hy
        rw [hAPQ] at ha'
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
        rcases ha' with rfl | rfl
        · exact Or.inl hya
        · exact Or.inr hya
      have hAll : 4 ≤ secondSmallestDegree G → ∀ y ∈ ({u, v, w} : Finset V),
          G.Adj y (l.getD P x₀) ∧ G.Adj y (l.getD Q x₀) :=
        fun h y hy => ⟨hS6 y hy (by omega) P hPA, hS6 y hy (by omega) Q hQA⟩
      have hcr := hcross P hPA Q hQA (by omega)
      have hs34 : (secondSmallestDegree G = 3 ∧ l.length = 9) ∨ (secondSmallestDegree G = 4 ∧ l.length = 10) ∨
          (secondSmallestDegree G = 4 ∧ l.length = 11) := by omega
      exact b21_fin2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 P Q i₀ hs34 (by omega) (by omega) hPQ hi₀b hLP hLQ hRP hRQ hMPQ hi₀ hAny hAll hcr
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h hAab
    · exact key b a h (by rw [hAab]; exact Finset.pair_comm a b)
  · obtain ⟨a, b, c, hab, hac, hbc, hAabc⟩ := Finset.card_eq_three.mp hr
    have hAe : ∀ x, x ∈ A ↔ x = a ∨ x = b ∨ x = c := by
      intro x; rw [hAabc]; simp
    have haA : a ∈ A := (hAe a).2 (Or.inl rfl)
    have hbA : b ∈ A := (hAe b).2 (Or.inr (Or.inl rfl))
    have hcA : c ∈ A := (hAe c).2 (Or.inr (Or.inr rfl))
    have hσ5 : secondSmallestDegree G = 5 := by omega
    have hm13 : l.length = 13 := by omega
    have hAll3 : ∀ y ∈ ({u, v, w} : Finset V), ∀ x ∈ A, G.Adj y (l.getD x x₀) :=
      fun y hy x hx => hS6 y hy (by omega) x hx
    have e1 := hS1 a haA
    have e2 := hS1 b hbA
    have e3 := hS1 c hcA
    have hLa := hL a haA
    have hLb := hL b hbA
    have hLc := hL c hcA
    have hRa := hRt a haA
    have hRb := hRt b hbA
    have hRc := hRt c hcA
    have mab := hM a haA b hbA
    have mba := hM b hbA a haA
    have mac := hM a haA c hcA
    have mca := hM c hcA a haA
    have mbc := hM b hbA c hcA
    have mcb := hM c hcA b hbA
    have hvals : (i₀ = 8 ∧ (a = 3 ∨ a = 7 ∨ a = 9) ∧ (b = 3 ∨ b = 7 ∨ b = 9) ∧ (c = 3 ∨ c = 7 ∨ c = 9)) ∨
        (i₀ = 4 ∧ (a = 3 ∨ a = 5 ∨ a = 9) ∧ (b = 3 ∨ b = 5 ∨ b = 9) ∧ (c = 3 ∨ c = 5 ∨ c = 9)) := by
      omega
    rcases hvals with ⟨hi8, -, -, -⟩ | ⟨hi4, -, -, -⟩
    · have m3 : 3 ∈ A := by rw [hAe]; omega
      have m7 : 7 ∈ A := by rw [hAe]; omega
      have m9 : 9 ∈ A := by rw [hAe]; omega
      exact Cadre.C10 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ5 hm13 u v w hR huv hvw huw h1 h2 h3
        (fun y hy => ⟨hAll3 y hy 3 m3, hAll3 y hy 7 m7, hAll3 y hy 9 m9⟩) (by subst hi8; exact hi₀)
    · have m3 : 3 ∈ A := by rw [hAe]; omega
      have m5 : 5 ∈ A := by rw [hAe]; omega
      have m9 : 9 ∈ A := by rw [hAe]; omega
      exact b21_fin3r hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 hσ5 hm13
        (fun y hy => ⟨hAll3 y hy 3 m3, hAll3 y hy 5 m5, hAll3 y hy 9 m9⟩) (by subst hi4; exact hi₀)
-- <</B21>>

-- <<B23>>
lemma b23_getD_inj {l : List V} (hnd : l.Nodup) (x₀ : V) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : l.getD i x₀ = l.getD j x₀) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (List.Nodup.getElem_inj_iff hnd).mp h

lemma b23_gamma (P : ℕ → Prop) (m : ℕ) (Jz Ja : Finset ℕ) (hJ : Jz.Nonempty)
    (hbd : ∀ j ∈ Jz, 0 < j ∧ j + 1 < m)
    (hpr1 : ∀ j ∈ Jz, j ≠ Jz.max' hJ → j + 2 ∈ Jz)
    (hpr2 : ∀ j ∈ Jz, j ≠ Jz.min' hJ → 2 ≤ j ∧ j - 2 ∈ Jz)
    (hsub : Ja ⊆ Jz) (hβ : ∀ j, j ∈ Jz → j + 2 ∈ Jz → (j ∈ Ja ∨ j + 2 ∈ Ja) → P (j + 1))
    (hinj : ∀ i i', i < m → i' < m → P i → P i' → i = i')
    (h5a : ∀ j ∈ Jz, j + 1 ∉ Jz) (hca : 2 ≤ Ja.card) (hcz : 3 ≤ Jz.card) : False := by
  have key : ∀ j ∈ Ja, j = Jz.max' hJ ∨ j = Jz.min' hJ := by
    intro j hj
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hjz := hsub hj
    have e1 := hpr1 j hjz h1
    obtain ⟨h2a, e2⟩ := hpr2 j hjz h2
    have p1 : P (j + 1) := hβ j hjz e1 (Or.inl hj)
    have e3 : j - 2 + 2 = j := Nat.sub_add_cancel h2a
    have p2 : P (j - 2 + 1) := hβ (j - 2) e2 (by rw [e3]; exact hjz)
      (Or.inr (by rw [e3]; exact hj))
    have hb1 := (hbd j hjz).2
    have := hinj _ _ (by omega) (by omega) p1 p2
    omega
  have hsub2 : Ja ⊆ {Jz.max' hJ, Jz.min' hJ} := by
    intro j hj
    rcases key j hj with h | h <;> simp [h]
  have hc2 := Finset.card_le_card hsub2
  have hne : Jz.max' hJ ≠ Jz.min' hJ := by
    intro h
    rw [h] at hc2
    simp at hc2
    omega
  have hEq : Ja = {Jz.max' hJ, Jz.min' hJ} :=
    Finset.eq_of_subset_of_card_le hsub2 (by rw [Finset.card_pair hne]; omega)
  have hMa : Jz.max' hJ ∈ Ja := by rw [hEq]; simp
  have hma : Jz.min' hJ ∈ Ja := by rw [hEq]; simp
  have hmz : Jz.min' hJ ∈ Jz := Finset.min'_mem _ _
  have hMz : Jz.max' hJ ∈ Jz := Finset.max'_mem _ _
  have hlt : Jz.min' hJ < Jz.max' hJ :=
    lt_of_le_of_ne (Finset.min'_le _ _ hMz) (Ne.symm hne)
  have e1 := hpr1 _ hmz (ne_of_lt hlt)
  obtain ⟨h2a, e2⟩ := hpr2 _ hMz hne
  have p1 : P (Jz.min' hJ + 1) := hβ _ hmz e1 (Or.inl hma)
  have e3 : Jz.max' hJ - 2 + 2 = Jz.max' hJ := Nat.sub_add_cancel h2a
  have p2 : P (Jz.max' hJ - 2 + 1) := hβ _ e2 (by rw [e3]; exact hMz)
    (Or.inr (by rw [e3]; exact hMa))
  have hb1 := (hbd _ hMz).2
  have hb2 := (hbd _ hmz).2
  have h22 := hinj _ _ (by omega) (by omega) p1 p2
  have hM : Jz.max' hJ = Jz.min' hJ + 2 := by omega
  have hsub3 : Jz ⊆ {Jz.min' hJ, Jz.min' hJ + 2} := by
    intro j hj
    have h1 := Finset.min'_le _ _ hj
    have h2 := Finset.le_max' _ _ hj
    have h3 : j ≠ Jz.min' hJ + 1 := by
      intro h; exact h5a _ hmz (h ▸ hj)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have := Finset.card_le_card hsub3
  have h4 := Finset.card_le_two (a := Jz.min' hJ) (b := Jz.min' hJ + 2)
  omega

lemma Cadre.R4_nonclique [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (z z' a b : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {z, z', a, b}) (hd : z ≠ z' ∧ z ≠ a ∧ z ≠ b ∧ z' ≠ a ∧ z' ≠ b ∧ a ≠ b)
    (hzz : ¬ G.Adj z z') (h1 : G.Adj z a) (h2 : G.Adj z b) (h3 : G.Adj z' a) (h4 : G.Adj z' b)
    (hm : l.length = 2 * secondSmallestDegree G + 2) : False := by
  classical
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  have hmemR : ∀ t, t ∉ l ↔ t ∈ ({z, z', a, b} : Finset V) := by
    intro t; rw [← hR]; simp
  have hz : z ∉ l := (hmemR z).mpr (by simp)
  have hz' : z' ∉ l := (hmemR z').mpr (by simp)
  have ha : a ∉ l := (hmemR a).mpr (by simp)
  have hbl : b ∉ l := (hmemR b).mpr (by simp)
  have hirr : ∀ t : V, ¬ G.Adj t t := fun t => G.loopless.irrefl t
  have hm0 : 0 < l.length := List.length_pos_of_ne_nil hne
  -- sigma >= 4
  have hσ4 : 4 ≤ secondSmallestDegree G := by
    by_contra hlt4
    push Not at hlt4
    have hcardR : (Finset.univ.filter (fun t => t ∉ l)).card = 4 := by
      rw [hR]; simp [Finset.card_insert_of_notMem, d1, d2, d3, d4, d5, d6]
    have hham : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∃ s : List V, s.Nodup ∧
        s.IsChain G.Adj ∧ s.toFinset = (Finset.univ.filter (fun t => t ∉ l)) ∧
        s.getLast? = some y := by
      intro y hy
      rw [hR] at hy ⊢
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h | h | h <;> rw [h]
      · refine ⟨[a, z', b, z], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm]
        · ext t; simp <;> tauto
        · simp
      · refine ⟨[a, z, b, z'], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm]
        · ext t; simp; tauto
        · simp
      · refine ⟨[z, b, z', a], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm]
        · ext t; simp; tauto
        · simp
      · refine ⟨[z, a, z', b], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm]
        · ext t; simp <;> tauto
        · simp
    have hd2 : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∀ y' ∈ (Finset.univ.filter (fun t => t ∉ l)),
        y ≠ y' → G.Adj y y' ∨ ∃ w ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y w ∧ G.Adj w y' := by
      intro y hy y' hy' hne'
      rw [hR] at hy hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
      have hza : z ∈ (Finset.univ.filter (fun t => t ∉ l)) := by rw [hR]; simp
      have haa : a ∈ (Finset.univ.filter (fun t => t ∉ l)) := by rw [hR]; simp
      rcases hy with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;>
        rw [h, h'] at hne' <;> rw [h, h'] <;>
        first
        | exact absurd rfl hne'
        | exact Or.inl h1 | exact Or.inl h1.symm | exact Or.inl h2 | exact Or.inl h2.symm
        | exact Or.inl h3 | exact Or.inl h3.symm | exact Or.inl h4 | exact Or.inl h4.symm
        | exact Or.inr ⟨a, haa, h1, h3.symm⟩ | exact Or.inr ⟨a, haa, h3, h1.symm⟩
        | exact Or.inr ⟨z, hza, h1.symm, h2⟩ | exact Or.inr ⟨z, hza, h2.symm, h1⟩
    have := Cadre.small_sigma hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hham hd2
    omega
  -- degree facts
  have hdz := Cadre.degree_split (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch hmem
    hhd hlast hmax hlt hz
  have hda := Cadre.degree_split (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch hmem
    hhd hlast hmax hlt ha
  have hx0ne : ∀ y, y ∉ l → y ≠ x₀ := fun y hy h => hy (h ▸ hmem)
  have hσz := hx0 z (hx0ne z hz)
  have hσa := hx0 a (hx0ne a ha)
  have hNz : ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj z)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card (t := {a, b}) ?_) Finset.card_le_two
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have := (hmemR t).mp ht1
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    rcases this with h | h | h | h
    · subst h; exact absurd ht2 (hirr _)
    · subst h; exact absurd ht2 hzz
    · exact Or.inl h
    · exact Or.inr h
  have hNa : ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj a)).card ≤ 3 := by
    refine le_trans (Finset.card_le_card (t := {z, z', b}) ?_) Finset.card_le_three
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have := (hmemR t).mp ht1
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    rcases this with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst h; exact absurd ht2 (hirr _)
    · exact Or.inr (Or.inr h)
  set Jz := (Finset.range l.length).filter (fun i => G.Adj z (l.getD i x₀)) with hJz
  set Ja := (Finset.range l.length).filter (fun i => G.Adj a (l.getD i x₀)) with hJa
  have hbdz : ∀ j ∈ Jz, 0 < j ∧ j + 1 < l.length := fun j hj =>
    Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hz hj
  have hbda : ∀ j ∈ Ja, 0 < j ∧ j + 1 < l.length := fun j hj =>
    Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt ha hj
  -- alpha
  set Bp : Finset V := l.toFinset.filter (fun x => ¬ G.Adj z x ∧ G.Adj a x) with hBp
  have hB : ∀ w ∈ Bp, w ∈ l ∧ ¬ G.Adj z w ∧ ∃ r, r ∉ l ∧ G.Adj z r ∧ G.Adj r w := by
    intro w hw
    simp only [hBp, Finset.mem_filter, List.mem_toFinset] at hw
    exact ⟨hw.1, hw.2.1, a, ha, h1, hw.2.2⟩
  have hK : ∀ w ∈ ({z'} : Finset V), w ∉ l ∧ w ≠ z ∧ ¬ G.Adj z w ∧ ∃ r, G.Adj z r ∧ G.Adj r w := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ⟨hz', Ne.symm d1, hzz, a, h1, h3.symm⟩
  have hB9 := Cadre.count_Q2 (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch hmem
    hhd hlast hmax hlt z hz Bp {z'} hB hK
  rw [← hJz] at hB9
  have hring := ring_card Jz (fun h0 => by have := (hbdz 0 h0).1; omega)
  have hJne : Jz.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; rw [h] at hdz; simp at hdz; omega
  have hTl := T_lt Jz hJne
  rw [Finset.card_singleton] at hB9
  have hBp0 : Bp.card = 0 := by omega
  have htz : (Jz.filter (fun j => j + 2 ∈ Jz)).card + 1 = Jz.card := by omega
  have hczσ : Jz.card + 2 = secondSmallestDegree G := by omega
  have hsub : Ja ⊆ Jz := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi)
    have hil := Finset.mem_range.mp hi'.1
    by_contra hnz
    have hmemB : l.getD i x₀ ∈ Bp := by
      simp only [hBp, Finset.mem_filter, List.mem_toFinset]
      refine ⟨?_, ?_, hi'.2⟩
      · rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem _
      · intro hadj; exact hnz (Finset.mem_filter.mpr ⟨hi'.1, hadj⟩)
    rw [Finset.card_eq_zero] at hBp0
    rw [hBp0] at hmemB
    simp at hmemB
  obtain ⟨hpr1, hpr2⟩ := prog Jz hJne htz
  -- beta
  have hβ : ∀ j, j ∈ Jz → j + 2 ∈ Jz → (j ∈ Ja ∨ j + 2 ∈ Ja) → l.getD (j + 1) x₀ = x₀ := by
    intro j hj hj2 hja
    by_contra hxj
    have hjb := hbdz j hj
    have hj2b := hbdz (j + 2) hj2
    have hzj : G.Adj z (l.getD j x₀) := (Finset.mem_filter.mp hj).2
    have hzj2 : G.Adj z (l.getD (j + 2) x₀) := (Finset.mem_filter.mp hj2).2
    have hxs : ∀ i, j < i → i < j + 2 → l.getD i x₀ ≠ x₀ := by
      intro i hi1 hi2
      have : i = j + 1 := by omega
      rw [this]; exact hxj
    rcases hja with h | h
    · have haj : G.Adj a (l.getD j x₀) := (Finset.mem_filter.mp h).2
      exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [a, z]
        (by simp) (by simp [d2, Ne.symm d2]) (by simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm])
        (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
        j (j + 2) (by omega) (by omega) haj.symm hzj2 hxs (by simp)
    · have haj : G.Adj a (l.getD (j + 2) x₀) := (Finset.mem_filter.mp h).2
      exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [z, a]
        (by simp) (by simp [d2, Ne.symm d2]) (by simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm])
        (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
        j (j + 2) (by omega) (by omega) hzj.symm haj hxs (by simp)
  have h5a : ∀ j ∈ Jz, j + 1 ∉ Jz := by
    intro j hj hj1
    have hzj : G.Adj z (l.getD j x₀) := (Finset.mem_filter.mp hj).2
    have hzj1 : G.Adj z (l.getD (j + 1) x₀) := (Finset.mem_filter.mp hj1).2
    have hjb := hbdz (j + 1) hj1
    exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [z]
      (by simp) (by simp) (by simp) (by intro v hv; simp at hv; subst hv; exact hz)
      j (j + 1) (by omega) (by omega) hzj.symm hzj1 (by intro i h1 h2; omega) (by simp)
  have hinj : ∀ i i', i < l.length → i' < l.length → l.getD i x₀ = x₀ → l.getD i' x₀ = x₀ →
      i = i' := fun i i' hi hi' e e' => b23_getD_inj hnd x₀ hi hi' (e.trans e'.symm)
  have hcard_a : secondSmallestDegree G ≤ Ja.card + 3 := by omega
  by_cases h5 : 5 ≤ secondSmallestDegree G
  · exact b23_gamma (fun i => l.getD i x₀ = x₀) l.length Jz Ja hJne hbdz hpr1 hpr2 hsub hβ hinj h5a
      (by omega) (by omega)
  · have hσ4e : secondSmallestDegree G = 4 := by omega
    have hcz2 : Jz.card = 2 := by omega
    have hm10 : l.length = 10 := by omega
    have hlt2 : 1 < Jz.card := by omega
    have hmin' := Finset.min'_lt_max'_of_card Jz hlt2
    have hpz : Jz.min' hJne ∈ Jz := Finset.min'_mem _ _
    have hp2 : Jz.min' hJne + 2 ∈ Jz := hpr1 _ hpz (ne_of_lt hmin')
    set p := Jz.min' hJne with hp
    have hJeq : Jz = {p, p + 2} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> assumption
      · rw [hcz2, Finset.card_pair (by omega)]
    have hJane : Ja.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; rw [h] at hcard_a; simp at hcard_a; omega
    obtain ⟨j0, hj0⟩ := hJane
    have hj0z := hsub hj0
    rw [hJeq] at hj0z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj0z
    have hpb := hbdz p hpz
    have hpb2 := hbdz (p + 2) hp2
    have hP : l.getD (p + 1) x₀ = x₀ := by
      apply hβ p hpz hp2
      rcases hj0z with rfl | rfl
      · exact Or.inl hj0
      · exact Or.inr hj0
    have hzp : G.Adj z (l.getD p x₀) := (Finset.mem_filter.mp hpz).2
    have hzp2 : G.Adj z (l.getD (p + 2) x₀) := (Finset.mem_filter.mp hp2).2
    have hp4 : 4 ≤ p := by
      by_contra hlt4
      push Not at hlt4
      refine Cadre.no_pre hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [b, z', a, z]
        (by simp) ?_ ?_ ?_ p (by omega) hzp ?_ (by simp; omega)
      · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
          Ne.symm d5, Ne.symm d6]
      · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
        exact ⟨h4.symm, h3, h1.symm⟩
      · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> assumption
      · intro i hi he
        have := hinj i (p + 1) (by omega) (by omega) he hP
        omega
    refine Cadre.no_suf hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [z, a, z', b]
      (by simp) ?_ ?_ ?_ (p + 2) (by omega) hzp2.symm ?_ (by simp; omega)
    · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
        Ne.symm d5, Ne.symm d6]
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨h1, h3.symm, h4⟩
    · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> assumption
    · intro i hi hi2 he
      have := hinj i (p + 1) hi2 (by omega) he hP
      omega
-- <</B23>>

-- <<B24>>
lemma b24_c11 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 5) (hm : l.length = 12)
    (a b c d : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {a, b, c, d}) (hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hadj : G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d)
    (hA : ∀ y ∈ ({a, b, c, d} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 7 x₀))
    (hx : l.getD 1 x₀ = x₀) : False := by
  classical
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := id hd
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := id hadj
  have hmemR : ∀ t, t ∉ l ↔ t ∈ ({a, b, c, d} : Finset V) := by
    intro t; rw [← hR]; simp
  have hcardR : (Finset.univ.filter (fun t => t ∉ l)).card = 4 := by
    rw [hR]; simp [Finset.card_insert_of_notMem, d1, d2, d3, d4, d5, d6]
  have hirr : ∀ t : V, ¬ G.Adj t t := fun t => G.loopless.irrefl t
  have hclq : ∀ y y' : V, y ∉ l → y' ∉ l → y ≠ y' → G.Adj y y' := by
    intro y y' hy hy' hne'
    have hy2 := (hmemR y).mp hy
    have hy2' := (hmemR y').mp hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy2 hy2'
    rcases hy2 with h | h | h | h <;> rcases hy2' with h' | h' | h' | h' <;>
      rw [h, h'] at hne' <;> rw [h, h'] <;>
      first
      | exact absurd rfl hne'
      | assumption
      | exact SimpleGraph.Adj.symm (by assumption)
  have hother : ∀ y : V, y ∉ l → ∃ w, w ∉ l ∧ w ≠ y := by
    intro y hy
    have h1 : 1 < (Finset.univ.filter (fun t => t ∉ l)).card := by omega
    obtain ⟨w, hw', hwy⟩ := Finset.exists_mem_ne h1 y
    exact ⟨w, by simpa using hw', hwy⟩
  have hsd : ∀ y y' : V, 1 < ((Finset.univ.filter (fun t => t ∉ l)) \ {y, y'}).card := by
    intro y y'
    have h1 := Finset.le_card_sdiff ({y, y'} : Finset V) (Finset.univ.filter (fun t => t ∉ l))
    have h3 : ({y, y'} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  have hother2 : ∀ y y' : V, y ∉ l → y' ∉ l → ∃ w, w ∉ l ∧ w ≠ y ∧ w ≠ y' := by
    intro y y' hy hy'
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (hsd y y')
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hu
    exact ⟨u, hu.1, hu.2.1, hu.2.2⟩
  have hpath4 : ∀ y y' : V, y ∉ l → y' ∉ l → y ≠ y' → ∃ u v : V, u ∉ l ∧ v ∉ l ∧
      [y, u, v, y'].Nodup ∧ [y, u, v, y'].IsChain G.Adj := by
    intro y y' hy hy' hyy
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (hsd y y')
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hu hv
    refine ⟨u, v, hu.1, hv.1, ?_, ?_⟩
    · simp [hyy, huv, hu.2.1, hu.2.2, hv.2.1, hv.2.2, Ne.symm hu.2.1, Ne.symm hu.2.2,
        Ne.symm hv.2.1, Ne.symm hv.2.2]
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨hclq y u hy hu.1 (Ne.symm hu.2.1), hclq u v hu.1 hv.1 huv,
        hclq v y' hv.1 hy' hv.2.2⟩
  have hm12 : l.length = 12 := hm
  have hm0 : 0 < l.length := List.length_pos_of_ne_nil hne
  have hgd : ∀ (d d' : V) (i : ℕ), i < l.length → l.getD i d = l.getD i d' := by
    intro d d' i hi; rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]
  have hXmem : ∀ i, i < l.length → l.getD i x₀ ∈ l := by
    intro i hi; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hinj : ∀ i j, i < l.length → j < l.length → l.getD i x₀ = l.getD j x₀ → i = j :=
    fun i j hi hj h => b23_getD_inj hnd x₀ hi hj h
  have hhead : l.head hne = l.getD 0 x₀ := by
    cases l with
    | nil => exact absurd rfl hne
    | cons h t => rfl
  have hlastv : l.getLast hne = l.getD 11 x₀ := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
    congr 1; omega
  have hadjc : ∀ i, i + 1 < l.length → G.Adj (l.getD i x₀) (l.getD (i + 1) x₀) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
    exact List.isChain_iff_getElem.mp hch i hi
  have hmaxs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := lemma4x hconn l hne hnd hch hmaxs hlt (by omega)
  rw [hhead] at c1 c4
  rw [hlastv] at c2 c4
  have h5b : ∀ y, y ∉ l → ∀ j, j < l.length → G.Adj y (l.getD j x₀) →
      0 < j ∧ j + 1 < l.length ∧ ¬ G.Adj y (l.getD (j + 1) x₀) ∧ ¬ G.Adj y (l.getD (j - 1) x₀) ∧
      ¬ G.Adj (l.getD 0 x₀) (l.getD (j + 1) x₀) ∧ ¬ G.Adj (l.getD 11 x₀) (l.getD (j - 1) x₀) := by
    intro y hy j hj hadj'
    have := lemma5abx hconn l hne hnd hch hmaxs y hy j hj (by rwa [hgd y x₀ j hj])
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := this
    rw [hhead, hgd y x₀ (j + 1) t2] at t5
    rw [hlastv, hgd y x₀ (j - 1) (by omega)] at t6
    rw [hgd y x₀ (j + 1) t2] at t3
    rw [hgd y x₀ (j - 1) (by omega)] at t4
    exact ⟨t1, t2, t3, t4, t5, t6⟩
  have hRA : ∀ y, y ∉ l → G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 7 x₀) :=
    fun y hy => hA y ((hmemR y).mp hy)
  have ha : a ∉ l := (hmemR a).mpr (by simp)
  have hdist2 : ∀ y w z : V, y ≠ w → ¬ G.Adj y w → G.Adj y z → G.Adj z w → G.dist y w = 2 := by
    intro y w z hyw hnadj h1 h2
    have hle : G.dist y w ≤ 2 :=
      SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil))
    have hreach : G.Reachable y w :=
      ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)⟩
    have h0 : G.dist y w ≠ 0 := fun h => hyw ((SimpleGraph.Reachable.dist_eq_zero_iff hreach).mp h)
    have h1' : G.dist y w ≠ 1 := fun h => hnadj (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  have hdl : d ∉ l := (hmemR d).mpr (by simp)
  have hsl0 : ∀ t ∈ [a, b, c, d], t ∉ l := by
    intro t ht; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with h | h | h | h <;> rw [h] <;> exact (hmemR _).mpr (by simp)
  have hnd0 : [a, b, c, d].Nodup := by simp [d1, d2, d3, d4, d5, d6]
  have hch0 : [a, b, c, d].IsChain G.Adj := by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨e1, e4, e6⟩
  have c4' : ∀ j, j + 1 < l.length → G.Adj (l.getD 0 x₀) (l.getD (j + 1) x₀) →
      ¬ G.Adj (l.getD j x₀) (l.getD 11 x₀) := by
    intro j hj h hl'
    exact c4 j hj (by rw [hgd (l.getD 0 x₀) x₀ (j + 1) hj]; exact h)
      (by rw [hgd (l.getD 0 x₀) x₀ j (by omega)]; exact hl')
  have hne0 : l.getD 0 x₀ ≠ x₀ := hhead ▸ hhd
  have hdeg0 : 5 ≤ G.degree (l.getD 0 x₀) := by rw [← hσ]; exact hx0 _ hne0
  -- phase 1 : head
  have hE : ∀ j, 2 < j → j ≤ 6 → ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀) := by
    intro j h1 h2 hadj'
    exact Cadre.endE hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [a, b, c, d]
      (by simp) hnd0 hch0 hsl0 2 j h1 (by omega) hadj' (by simpa using (hRA d hdl).1)
      ⟨1, Or.inl (by omega), by omega, hx⟩ (by simp; omega)
  have hexcl : ∀ j, 0 < j → j < l.length → j ∉ ({1, 2, 7, 9, 10} : Finset ℕ) →
      ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀) := by
    intro j h0 h12 hj
    have hcases : (2 < j ∧ j ≤ 6) ∨ j = 8 ∨ j = 11 := by simp at hj; omega
    rcases hcases with ⟨h1, h2⟩ | rfl | rfl
    · exact hE j h1 h2
    · exact (h5b a ha 7 (by omega) (hRA a ha).2).2.2.2.2.1
    · intro hadj'
      exact c4' 10 (by omega) hadj' (hadjc 10 (by omega))
  have hle0 := Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    ({1, 2, 7, 9, 10} : Finset ℕ) hexcl
  have hcard5 : ({1, 2, 7, 9, 10} : Finset ℕ).card = 5 := by decide
  have hforced := Cadre.head_forced hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    ({1, 2, 7, 9, 10} : Finset ℕ) (by intro j hj; simp at hj; omega) hexcl (by omega)
  have hX02 : G.Adj (l.getD 0 x₀) (l.getD 2 x₀) := hforced 2 (by simp)
  -- phase 2 : last
  obtain ⟨S', hS'⟩ : ∃ S' : Finset V, S' = ({0, 1, 3, 6, 8} : Finset ℕ).image (fun i => l.getD i x₀) :=
    ⟨_, rfl⟩
  have hneA : ∀ i, i < l.length → a ≠ l.getD i x₀ := fun i hi h => ha (h ▸ hXmem i hi)
  have hdist : ∀ w ∈ S', G.dist a w = 2 := by
    intro w hw
    rw [hS'] at hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact hdist2 a _ (l.getD 2 x₀) (hneA _ (by omega)) (fun h => ha (c1 a h.symm))
        (hRA a ha).1 hX02.symm
    · exact hdist2 a _ (l.getD 2 x₀) (hneA _ (by omega))
        (h5b a ha 2 (by omega) (hRA a ha).1).2.2.2.1 (hRA a ha).1 (hadjc 1 (by omega)).symm
    · exact hdist2 a _ (l.getD 2 x₀) (hneA _ (by omega))
        (h5b a ha 2 (by omega) (hRA a ha).1).2.2.1 (hRA a ha).1 (hadjc 2 (by omega))
    · exact hdist2 a _ (l.getD 7 x₀) (hneA _ (by omega))
        (h5b a ha 7 (by omega) (hRA a ha).2).2.2.2.1 (hRA a ha).2 (hadjc 6 (by omega)).symm
    · exact hdist2 a _ (l.getD 7 x₀) (hneA _ (by omega))
        (h5b a ha 7 (by omega) (hRA a ha).2).2.2.1 (hRA a ha).2 (hadjc 7 (by omega))
  have hS'card : S'.card = 5 := by
    rw [hS', Finset.card_image_of_injOn]
    · decide
    · intro i hi j hj h
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi hj
      exact hinj i j (by omega) (by omega) h
  have hΓ : ∀ j, (j = 2 ∨ j = 7) → ¬ G.Adj (l.getD j x₀) (l.getD 11 x₀) := by
    intro j hj hadj'
    have hzj : G.Adj a (l.getD j x₀) := by
      rcases hj with rfl | rfl
      · exact (hRA a ha).1
      · exact (hRA a ha).2
    have hnot : l.getD 11 x₀ ∉ S' := by
      intro h
      rw [hS'] at h
      obtain ⟨i, hi, hi2⟩ := Finset.mem_image.mp h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      have := hinj i 11 (by omega) (by omega) hi2
      omega
    have hc := Finset.card_insert_of_notMem hnot
    have hb3 := card_le_gamma hconn hH a (insert (l.getD 11 x₀) S') (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact hdist2 a _ (l.getD j x₀) (hneA _ (by omega)) (fun h => ha (c2 a h.symm)) hzj
          hadj'
      · exact hdist w hw')
    omega
  have hexL : ∀ j, j + 1 < l.length → j ∉ ({8, 9, 10} : Finset ℕ) →
      ¬ G.Adj (l.getD j x₀) (l.getD (l.length - 1) x₀) := by
    intro j hj hnC hadj'
    have e11 : l.length - 1 = 11 := by omega
    rw [e11] at hadj'
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ (3 ≤ j ∧ j ≤ 6) ∨ j = 7 := by simp at hnC; omega
    rcases hcases with rfl | rfl | rfl | ⟨h1, h2⟩ | rfl
    · exact c4' 10 (by omega) hadj' (hadjc 10 (by omega))
    · exact (h5b a ha 2 (by omega) (hRA a ha).1).2.2.2.2.2 hadj'.symm
    · exact hΓ 2 (Or.inl rfl) hadj'
    · exact Cadre.endE_last hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [a, b, c, d]
        (by simp) hnd0 hch0 hsl0 7 j (by omega) (by omega) (by rw [e11]; exact hadj'.symm)
        (by simpa using (hRA a ha).2) ⟨1, Or.inr (by omega), by omega, hx⟩ (by simp; omega)
    · exact hΓ 7 (Or.inr rfl) hadj'
  have hleL := Cadre.last_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    ({8, 9, 10} : Finset ℕ) hexL
  have hcard3 : ({8, 9, 10} : Finset ℕ).card = 3 := by decide
  have hneL : l.getD (l.length - 1) x₀ ≠ x₀ := by
    have e11 : l.length - 1 = 11 := by omega
    rw [e11, ← hlastv]; exact hlast
  have hdegL : 5 ≤ G.degree (l.getD (l.length - 1) x₀) := by rw [← hσ]; exact hx0 _ hneL
  omega

lemma b24_core [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (a b c d : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {a, b, c, d}) (hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hadj : G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d)
    (hm : l.length = 2 * secondSmallestDegree G + 2)
    (hw : ∀ i, i < l.length → l.getD i x₀ = x₀ → 2 * i + 1 ≤ l.length) : False := by
  classical
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := id hd
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := id hadj
  have hmemR : ∀ t, t ∉ l ↔ t ∈ ({a, b, c, d} : Finset V) := by
    intro t; rw [← hR]; simp
  have hcardR : (Finset.univ.filter (fun t => t ∉ l)).card = 4 := by
    rw [hR]; simp [Finset.card_insert_of_notMem, d1, d2, d3, d4, d5, d6]
  have hirr : ∀ t : V, ¬ G.Adj t t := fun t => G.loopless.irrefl t
  have hclq : ∀ y y' : V, y ∉ l → y' ∉ l → y ≠ y' → G.Adj y y' := by
    intro y y' hy hy' hne'
    have hy2 := (hmemR y).mp hy
    have hy2' := (hmemR y').mp hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy2 hy2'
    rcases hy2 with h | h | h | h <;> rcases hy2' with h' | h' | h' | h' <;>
      rw [h, h'] at hne' <;> rw [h, h'] <;>
      first
      | exact absurd rfl hne'
      | assumption
      | exact SimpleGraph.Adj.symm (by assumption)
  have hother : ∀ y : V, y ∉ l → ∃ w, w ∉ l ∧ w ≠ y := by
    intro y hy
    have h1 : 1 < (Finset.univ.filter (fun t => t ∉ l)).card := by omega
    obtain ⟨w, hw', hwy⟩ := Finset.exists_mem_ne h1 y
    exact ⟨w, by simpa using hw', hwy⟩
  have hsd : ∀ y y' : V, 1 < ((Finset.univ.filter (fun t => t ∉ l)) \ {y, y'}).card := by
    intro y y'
    have h1 := Finset.le_card_sdiff ({y, y'} : Finset V) (Finset.univ.filter (fun t => t ∉ l))
    have h3 : ({y, y'} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  have hother2 : ∀ y y' : V, y ∉ l → y' ∉ l → ∃ w, w ∉ l ∧ w ≠ y ∧ w ≠ y' := by
    intro y y' hy hy'
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (hsd y y')
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hu
    exact ⟨u, hu.1, hu.2.1, hu.2.2⟩
  have hpath4 : ∀ y y' : V, y ∉ l → y' ∉ l → y ≠ y' → ∃ u v : V, u ∉ l ∧ v ∉ l ∧
      [y, u, v, y'].Nodup ∧ [y, u, v, y'].IsChain G.Adj := by
    intro y y' hy hy' hyy
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (hsd y y')
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hu hv
    refine ⟨u, v, hu.1, hv.1, ?_, ?_⟩
    · simp [hyy, huv, hu.2.1, hu.2.2, hv.2.1, hv.2.2, Ne.symm hu.2.1, Ne.symm hu.2.2,
        Ne.symm hv.2.1, Ne.symm hv.2.2]
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨hclq y u hy hu.1 (Ne.symm hu.2.1), hclq u v hu.1 hv.1 huv,
        hclq v y' hv.1 hy' hv.2.2⟩
  -- sigma >= 4
  have hσ4 : 4 ≤ secondSmallestDegree G := by
    by_contra hlt4
    push Not at hlt4
    have hham : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∃ s : List V, s.Nodup ∧
        s.IsChain G.Adj ∧ s.toFinset = (Finset.univ.filter (fun t => t ∉ l)) ∧
        s.getLast? = some y := by
      intro y hy
      rw [hR] at hy ⊢
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h | h | h <;> rw [h]
      · refine ⟨[b, c, d, a], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, e1, e1.symm, e2, e2.symm, e3, e3.symm, e4, e4.symm,
            e5, e5.symm, e6, e6.symm]
        · ext t; simp <;> tauto
        · simp
      · refine ⟨[a, c, d, b], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, e1, e1.symm, e2, e2.symm, e3, e3.symm, e4, e4.symm,
            e5, e5.symm, e6, e6.symm]
        · ext t; simp <;> tauto
        · simp
      · refine ⟨[a, b, d, c], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, e1, e1.symm, e2, e2.symm, e3, e3.symm, e4, e4.symm,
            e5, e5.symm, e6, e6.symm]
        · ext t; simp <;> tauto
        · simp
      · refine ⟨[a, b, c, d], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, e1, e1.symm, e2, e2.symm, e3, e3.symm, e4, e4.symm,
            e5, e5.symm, e6, e6.symm]
        · ext t; simp <;> tauto
        · simp
    have hd2 : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∀ y' ∈ (Finset.univ.filter (fun t => t ∉ l)),
        y ≠ y' → G.Adj y y' ∨ ∃ w ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y w ∧ G.Adj w y' := by
      intro y hy y' hy' hne'
      exact Or.inl (hclq y y' (by simpa using hy) (by simpa using hy') hne')
    have := Cadre.small_sigma hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hham hd2
    omega
  -- index sets
  have hm0 : 0 < l.length := List.length_pos_of_ne_nil hne
  obtain ⟨Jf, hJf⟩ : ∃ Jf : V → Finset ℕ, ∀ y, Jf y =
      (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, fun _ => rfl⟩
  have hJm : ∀ y i, i ∈ Jf y ↔ i < l.length ∧ G.Adj y (l.getD i x₀) := by
    intro y i; rw [hJf]; simp
  obtain ⟨A, hAm'⟩ : ∃ A : Finset ℕ, ∀ i, i ∈ A ↔
      i < l.length ∧ ∃ y, y ∉ l ∧ G.Adj y (l.getD i x₀) :=
    ⟨(Finset.range l.length).filter (fun i => ∃ y, y ∉ l ∧ G.Adj y (l.getD i x₀)),
      fun i => by simp⟩
  have hbnd : ∀ y, y ∉ l → ∀ j, j < l.length → G.Adj y (l.getD j x₀) →
      0 < j ∧ j + 1 < l.length := by
    intro y hy j hj hadj'
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
      (by rw [← hJf]; exact (hJm y j).mpr ⟨hj, hadj'⟩)
  have hJA : ∀ y, y ∉ l → Jf y ⊆ A := by
    intro y hy i hi
    obtain ⟨h1, h2⟩ := (hJm y i).mp hi
    exact (hAm' i).mpr ⟨h1, y, hy, h2⟩
  have hAm : ∀ i ∈ A, 1 ≤ i ∧ i + 2 ≤ l.length := by
    intro i hi
    obtain ⟨h1, y, hy, h2⟩ := (hAm' i).mp hi
    have := hbnd y hy i h1 h2
    omega
  -- degrees
  have hdegJ : ∀ y, y ∉ l → secondSmallestDegree G ≤ (Jf y).card + 3 := by
    intro y hy
    have hds := Cadre.degree_split (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch
      hmem hhd hlast hmax hlt hy
    rw [← hJf] at hds
    have hyx : y ≠ x₀ := fun h => hy (h ▸ hmem)
    have hσy := hx0 y hyx
    have hN : ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card ≤ 3 := by
      have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) ⊆
          (Finset.univ.filter (fun t => t ∉ l)).erase y := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [Finset.mem_erase]
        refine ⟨?_, ht.1⟩
        rintro rfl
        exact hirr _ ht.2
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (by simpa using hy)] at h1
      omega
    omega
  have hXmem : ∀ i, i < l.length → l.getD i x₀ ∈ l := by
    intro i hi; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hinj : ∀ i j, i < l.length → j < l.length → l.getD i x₀ = l.getD j x₀ → i = j :=
    fun i j hi hj h => b23_getD_inj hnd x₀ hi hj h
  -- |A \ J y| <= 2
  have hAJ : ∀ y, y ∉ l → (A \ Jf y).card ≤ 2 := by
    intro y hy
    obtain ⟨Bp, hBp⟩ : ∃ Bp : Finset V, ∀ w, w ∈ Bp ↔ w ∈ l ∧ ¬ G.Adj y w ∧ ∃ w2, w2 ∉ l ∧ G.Adj w2 w :=
      ⟨l.toFinset.filter (fun w => ¬ G.Adj y w ∧ ∃ w2, w2 ∉ l ∧ G.Adj w2 w), fun w => by simp⟩
    have hB : ∀ w ∈ Bp, w ∈ l ∧ ¬ G.Adj y w ∧ ∃ z, z ∉ l ∧ G.Adj y z ∧ G.Adj z w := by
      intro w hw
      obtain ⟨h1, h2, w2, hw2, h3⟩ := (hBp w).mp hw
      refine ⟨h1, h2, w2, hw2, ?_, h3⟩
      have hne2 : y ≠ w2 := by rintro rfl; exact h2 h3
      exact hclq y w2 hy hw2 hne2
    have hK : ∀ w ∈ (∅ : Finset V), w ∉ l ∧ w ≠ y ∧ ¬ G.Adj y w ∧ ∃ z, G.Adj y z ∧ G.Adj z w := by
      intro w hw; simp at hw
    have hB9 := Cadre.count_Q2 (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch hmem
      hhd hlast hmax hlt y hy Bp ∅ hB hK
    rw [← hJf] at hB9
    have hdg := hdegJ y hy
    have hJne : (Jf y).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; rw [h] at hdg; simp at hdg; omega
    have hring := ring_card (Jf y) (fun h0 => by
      have := (hJm y 0).mp h0
      have := hbnd y hy 0 this.1 this.2
      omega)
    have hTl := T_lt (Jf y) hJne
    have hcardle : (A \ Jf y).card ≤ Bp.card := by
      apply Finset.card_le_card_of_injOn (fun i => l.getD i x₀)
      · intro i hi
        rw [Finset.mem_coe, Finset.mem_sdiff] at hi
        obtain ⟨hiA, hiJ⟩ := hi
        obtain ⟨hil, w2, hw2, hw2a⟩ := (hAm' i).mp hiA
        rw [Finset.mem_coe, hBp]
        refine ⟨hXmem i hil, ?_, w2, hw2, hw2a⟩
        intro hadj'
        exact hiJ ((hJm y i).mpr ⟨hil, hadj'⟩)
      · intro i hi j hj hij
        rw [Finset.mem_coe, Finset.mem_sdiff] at hi hj
        obtain ⟨hil, _⟩ := (hAm' i).mp hi.1
        obtain ⟨hjl, _⟩ := (hAm' j).mp hj.1
        exact hinj i j hil hjl hij
    simp only [Finset.card_empty] at hB9
    omega
  -- position of x0
  obtain ⟨i₀, hi₀l, hi₀⟩ : ∃ i, i < l.length ∧ l.getD i x₀ = x₀ := by
    obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact hx⟩
  have hX0 : ∀ i, i < l.length → l.getD i x₀ = x₀ → i = i₀ :=
    fun i hi he => hinj i i₀ hi hi₀l (he.trans hi₀.symm)
  have hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ l.length := by
    have h0 : l.getD 0 x₀ = l.head hne := by
      cases l with
      | nil => exact absurd rfl hne
      | cons h t => rfl
    have h1 : l.getD (l.length - 1) x₀ = l.getLast hne := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
    have hn0 : i₀ ≠ 0 := by
      intro h; rw [h] at hi₀; exact hhd (h0 ▸ hi₀)
    have hn1 : i₀ ≠ l.length - 1 := by
      intro h; rw [h] at hi₀; exact hlast (h1 ▸ hi₀)
    omega
  obtain ⟨E, hE'⟩ : ∃ E : Finset ℕ, ∀ x, x ∈ E ↔ x ∈ A ∧ ∃ x2 ∈ A, x < x2 ∧
      (∀ z ∈ A, ¬ (x < z ∧ z < x2)) ∧ ∃ w, w ∉ l ∧ ∀ w', w' ∉ l →
        (G.Adj w' (l.getD x x₀) ∨ G.Adj w' (l.getD x2 x₀)) → w' = w :=
    ⟨A.filter (fun x => ∃ x2 ∈ A, x < x2 ∧ (∀ z ∈ A, ¬ (x < z ∧ z < x2)) ∧ ∃ w, w ∉ l ∧
      ∀ w', w' ∉ l → (G.Adj w' (l.getD x x₀) ∨ G.Adj w' (l.getD x2 x₀)) → w' = w),
      fun x => by simp [Finset.mem_filter]⟩
  have hEA : E ⊆ A := fun x hx => ((hE' x).mp hx).1
  -- gaps
  have hM : ∀ x ∈ A, ∀ y ∈ A, x < y → (∀ z ∈ A, ¬ (x < z ∧ z < y)) →
      x + 2 ≤ y ∧ (x ∉ E → x + 4 + 1 ≤ y ∨ (x < i₀ ∧ i₀ < y)) := by
    intro x hx y hy hxy hcons
    obtain ⟨hxl, wx, hwx, hxw⟩ := (hAm' x).mp hx
    obtain ⟨hyl, wy, hwy, hyw⟩ := (hAm' y).mp hy
    constructor
    · by_contra hlt2
      have hy1 : y = x + 1 := by omega
      by_cases hww : wx = wy
      · subst hww
        exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [wx]
          (by simp) (by simp) (by simp)
          (by intro v hv; simp at hv; subst hv; exact hwx) x y hxy hyl hxw.symm hyw
          (by intro i h1 h2; omega) (by simp only [List.length_singleton]; omega)
      · exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [wx, wy]
          (by simp) (by simp [hww])
          (by simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
              exact hclq wx wy hwx hwy hww)
          (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
          x y hxy hyl hxw.symm hyw
          (by intro i h1 h2; omega) (by simp; omega)
    · intro hxE
      by_contra hcon
      push Not at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      have hyx5 : y < x + 5 := by omega
      have hxnx : ∀ i, x < i → i < y → l.getD i x₀ ≠ x₀ := by
        intro i h1 h2 he
        have := hX0 i (by omega) he
        have := hc2 (by omega)
        omega
      obtain ⟨u, v, hu, hv, huv, hu1, hv1⟩ : ∃ u v : V, u ∉ l ∧ v ∉ l ∧ u ≠ v ∧
          G.Adj u (l.getD x x₀) ∧ G.Adj v (l.getD y x₀) := by
        by_cases hww : wx = wy
        · subst hww
          have key : ∃ w, w ∉ l ∧ (G.Adj w (l.getD x x₀) ∨ G.Adj w (l.getD y x₀)) ∧ w ≠ wx := by
            by_contra hno
            push Not at hno
            exact hxE ((hE' x).mpr ⟨hx, y, hy, hxy, hcons, wx, hwx, fun w hw h => hno w hw h⟩)
          obtain ⟨w, hw, hwa, hwne⟩ := key
          rcases hwa with h | h
          · exact ⟨w, wx, hw, hwx, hwne, h, hyw⟩
          · exact ⟨wx, w, hwx, hw, hwne.symm, hxw, h⟩
        · exact ⟨wx, wy, hwx, hwy, hww, hxw, hyw⟩
      obtain ⟨p, q, hp, hq, hnd4, hch4⟩ := hpath4 u v hu hv huv
      exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [u, p, q, v]
        (by simp) hnd4 hch4
        (by intro t ht; simp at ht; rcases ht with rfl | rfl | rfl | rfl <;> assumption)
        x y hxy hyl hu1.symm hv1 hxnx (by simp; omega)
  -- |A| >= 2
  have hAne : A.Nonempty := by
    obtain ⟨x, y, hxy, hyl, ⟨w1, hw1, h1⟩, ⟨w2, hw2, h2⟩⟩ :=
      Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    exact ⟨x, (hAm' x).mpr ⟨by omega, w1, by simpa using hw1, h1⟩⟩
  have hA2 : 2 ≤ A.card := by
    obtain ⟨x, y, hxy, hyl, ⟨w1, hw1, h1⟩, ⟨w2, hw2, h2⟩⟩ :=
      Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hxA : x ∈ A := (hAm' x).mpr ⟨by omega, w1, by simpa using hw1, h1⟩
    have hyA : y ∈ A := (hAm' y).mpr ⟨hyl, w2, by simpa using hw2, h2⟩
    have : ({x, y} : Finset ℕ) ⊆ A := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    have h3 := Finset.card_le_card this
    rwa [Finset.card_pair (by omega)] at h3
  -- ends
  have hL : 4 ≤ A.min' hAne ∨ i₀ < A.min' hAne := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hminA := Finset.min'_mem A hAne
    obtain ⟨hml, wy, hwy, hyw⟩ := (hAm' _).mp hminA
    obtain ⟨y2, hy2, hy2y⟩ := hother wy hwy
    obtain ⟨u, v, hu, hv, hnd4, hch4⟩ := hpath4 y2 wy hy2 hwy hy2y
    exact Cadre.no_pre hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y2, u, v, wy]
      (by simp) hnd4 hch4
      (by intro t ht; simp at ht; rcases ht with rfl | rfl | rfl | rfl <;> assumption)
      (A.min' hAne) hml (by simpa using hyw)
      (by intro i hi' he; have := hX0 i (by omega) he; omega) (by simp; omega)
  have hR' : A.max' hAne + 4 + 1 ≤ l.length ∨ A.max' hAne < i₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hmaxA := Finset.max'_mem A hAne
    obtain ⟨hml, wy, hwy, hyw⟩ := (hAm' _).mp hmaxA
    obtain ⟨y2, hy2, hy2y⟩ := hother wy hwy
    obtain ⟨u, v, hu, hv, hnd4, hch4⟩ := hpath4 wy y2 hwy hy2 (Ne.symm hy2y)
    exact Cadre.no_suf hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [wy, u, v, y2]
      (by simp) hnd4 hch4
      (by intro t ht; simp at ht; rcases ht with rfl | rfl | rfl | rfl <;> assumption)
      (A.max' hAne) hml (by simpa using hyw.symm)
      (by intro i hi1 hi2 he; have := hX0 i hi2 he; omega) (by simp; omega)
  -- |E| <= 1
  have hE2 : ∀ x ∈ E, ∀ y ∈ E, x < y → False := by
    intro x hx y hy hxy
    obtain ⟨hxA, x2, hx2, hxx2, hcx, wx, hwx, hwxall⟩ := (hE' x).mp hx
    obtain ⟨hyA, y2, hy2, hyy2, hcy, wy, hwy, hwyall⟩ := (hE' y).mp hy
    obtain ⟨w, hw, hw1, hw2⟩ := hother2 wx wy hwx hwy
    have hn1 : ¬ G.Adj w (l.getD x x₀) := fun h => hw1 (hwxall w hw (Or.inl h))
    have hn2 : ¬ G.Adj w (l.getD y x₀) := fun h => hw2 (hwyall w hw (Or.inl h))
    have hn3 : ¬ G.Adj w (l.getD y2 x₀) := fun h => hw2 (hwyall w hw (Or.inr h))
    have hsub3 : ({x, y, y2} : Finset ℕ) ⊆ A \ Jf w := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [Finset.mem_sdiff]
      rcases ht with rfl | rfl | rfl
      · exact ⟨hxA, fun h => hn1 ((hJm w _).mp h).2⟩
      · exact ⟨hyA, fun h => hn2 ((hJm w _).mp h).2⟩
      · exact ⟨hy2, fun h => hn3 ((hJm w _).mp h).2⟩
    have h3 := Finset.card_le_card hsub3
    rw [Finset.card_eq_three.mpr ⟨x, y, y2, by omega, by omega, by omega, rfl⟩] at h3
    have := hAJ w hw
    omega
  have hEcard : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hne2
    rcases lt_or_gt_of_ne hne2 with h | h
    · exact hE2 x hx y hy h
    · exact hE2 y hy x hx h
  have hEempty : (∀ y, y ∉ l → A ⊆ Jf y) → E.card = 0 := by
    intro hsup
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hxA, x2, hx2, hxx2, hcx, wx, hwx, hall⟩ := (hE' x).mp hx
    obtain ⟨w, hw, hwne⟩ := hother wx hwx
    exact hwne (hall w hw (Or.inl ((hJm w x).mp (hsup w hw hxA)).2))
  -- pack
  have hpack := pack A E l.length 4 i₀ (by norm_num) hAne hEA hAm hi hL hR' hM
  have ha : a ∉ l := (hmemR a).mpr (by simp)
  have hσA : secondSmallestDegree G ≤ A.card + 3 :=
    le_trans (hdegJ a ha) (by have := Finset.card_le_card (hJA a ha); omega)
  have hσ6 : secondSmallestDegree G ≤ 6 := by omega
  have hfull : A.card ≤ (secondSmallestDegree G) - 3 → ∀ y, y ∉ l → Jf y = A := by
    intro hr y hy
    exact Finset.eq_of_subset_of_card_le (hJA y hy) (by have := hdegJ y hy; omega)
  have hσcases : secondSmallestDegree G = 4 ∨ secondSmallestDegree G = 5 ∨
      secondSmallestDegree G = 6 := by omega
  rcases hσcases with h4 | h5 | h6
  · -- sigma = 4
    have hr2 : A.card = 2 := by omega
    have hE1 : 1 ≤ E.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
    obtain ⟨hxA, x2, hx2, hxx2, hcx, wx, hwx, hall⟩ := (hE' x).mp hx
    have hAeq : A = {x, x2} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> assumption
      · rw [hr2, Finset.card_pair (by omega)]
    obtain ⟨w, hw, hwne⟩ := hother wx hwx
    have hdw := hdegJ w hw
    obtain ⟨i, hi'⟩ := Finset.card_pos.mp (by omega : 0 < (Jf w).card)
    have hiA := hJA w hw hi'
    rw [hAeq] at hiA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiA
    have hadj' := ((hJm w i).mp hi').2
    rcases hiA with rfl | rfl
    · exact hwne (hall w hw (Or.inl hadj'))
    · exact hwne (hall w hw (Or.inr hadj'))
  · -- sigma = 5
    have hr2 : A.card = 2 := by omega
    have hfl := hfull (by omega)
    have hallA : ∀ y, y ∉ l → ∀ i ∈ A, G.Adj y (l.getD i x₀) := fun y hy i hi' =>
      ((hJm y i).mp (by rw [hfl y hy]; exact hi')).2
    have hE0 := hEempty (fun y hy i hi' => by rw [hfl y hy]; exact hi')
    have hm12 : l.length = 12 := by omega
    have hw' := hw i₀ hi₀l hi₀
    set P := A.min' hAne with hP
    set Q := A.max' hAne with hQ
    have hPA : P ∈ A := Finset.min'_mem A hAne
    have hQA : Q ∈ A := Finset.max'_mem A hAne
    have hPQ : P < Q := Finset.min'_lt_max'_of_card A (by omega)
    have hAeq : A = {P, Q} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> assumption
      · rw [hr2, Finset.card_pair (by omega)]
    have hcons : ∀ z ∈ A, ¬ (P < z ∧ z < Q) := by
      intro z hz hzz
      rw [hAeq] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      omega
    obtain ⟨hgap, hcross⟩ := hM P hPA Q hQA hPQ hcons
    have hPE : P ∉ E := by
      intro hmemE
      have := Finset.card_pos.mpr ⟨P, hmemE⟩
      omega
    have hcr := hcross hPE
    have hAmP := hAm P hPA
    have hAmQ := hAm Q hQA
    have hcardR4 := hcardR
    have hSmem : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), y ∉ l := by
      intro y hy; simpa using hy
    by_cases hx0A : i₀ = P ∨ i₀ = Q
    · have hi0A : i₀ ∈ A := by rcases hx0A with h | h <;> rw [h] <;> assumption
      have := Cadre.x0_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
        (Finset.univ.filter (fun t => t ∉ l)) hSmem i₀ hi.1 (by omega) hi₀
        (by intro y hy; have := hallA y (hSmem y hy) i₀ hi0A; rwa [hi₀] at this)
      omega
    · obtain ⟨y2, hy2, hy2a⟩ := hother a ha
      obtain ⟨u, v, hu, hv, hnd4, hch4⟩ := hpath4 a y2 ha hy2 (Ne.symm hy2a)
      have hsl : ∀ t ∈ [a, u, v, y2], t ∉ l := by
        intro t ht; simp at ht; rcases ht with rfl | rfl | rfl | rfl <;> assumption
      by_cases hq : Q = P + 2
      · have hi1 : i₀ = P + 1 := by omega
        have := Cadre.hole_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
          (Finset.univ.filter (fun t => t ∉ l)) hSmem P hAmP.1 (by omega)
          (by rw [← hi1]; exact hi₀)
          (fun y hy => Or.inl (hallA y (hSmem y hy) P hPA))
          [a, u, v, y2] (by simp) hnd4 hch4 hsl
          (by simpa using (hallA a ha P hPA).symm)
          (by rw [← hq]; simpa using (hallA y2 hy2 Q hQA))
        omega
      · have hcase : (i₀ = 1 ∧ P = 2 ∧ Q = 7) ∨ (i₀ = 5 ∧ P = 4 ∧ Q = 7) := by omega
        rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have h2A : 2 ∈ A := h2 ▸ hPA
          have h7A : 7 ∈ A := h3 ▸ hQA
          exact b24_c11 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt h5 hm12
            a b c d hR hd hadj
            (by intro y hy; exact ⟨hallA y ((hmemR y).mpr hy) 2 h2A, hallA y ((hmemR y).mpr hy) 7 h7A⟩)
            (h1 ▸ hi₀)
        · have h4A : 4 ∈ A := h2 ▸ hPA
          have h7A : 7 ∈ A := h3 ▸ hQA
          exact Cadre.walk_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
            [a, u, v, y2] (by simp) hnd4 hch4 hsl 4 7 (by omega) (by omega) (by omega)
            (by rw [show (4:ℕ) + 1 = i₀ by omega]; exact hi₀)
            (fun t ht => hallA t (hsl t ht) 4 h4A) (fun t ht => hallA t (hsl t ht) 7 h7A)
            (by simp; omega) (by simp)
  · -- sigma = 6
    have hr2 : A.card = 3 := by omega
    have hfl := hfull (by omega)
    have hE0 := hEempty (fun y hy i hi' => by rw [hfl y hy]; exact hi')
    omega

lemma Cadre.R4_clique [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (a b c d : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {a, b, c, d}) (hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hadj : G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d)
    (hm : l.length = 2 * secondSmallestDegree G + 2) : False := by
  classical
  by_cases hwl : ∀ i, i < l.length → l.getD i x₀ = x₀ → 2 * i + 1 ≤ l.length
  · exact b24_core hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt a b c d hR hd hadj
      hm hwl
  · obtain ⟨hne', hnd', hch', hmem', hhd', hlast', hmax', hlt'⟩ :=
      Cadre.reverse hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    refine b24_core (l := l.reverse) hconn hb hH hmin hx0 hδ hne' hnd' hch' hmem' hhd' hlast' hmax'
      hlt' a b c d ?_ hd hadj ?_ ?_
    · rw [← hR]; ext t; simp
    · rw [List.length_reverse]; exact hm
    · intro i hi he
      rw [List.length_reverse] at hi ⊢
      rw [Cadre.getD_reverse l x₀ hi] at he
      push Not at hwl
      obtain ⟨j, hj, hjx, hbad⟩ := hwl
      have := b23_getD_inj hnd x₀ (by omega) hj (he.trans hjx.symm)
      omega
-- <</B24>>

-- <<B24.C11>>
lemma Cadre.C11 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 5) (hm : l.length = 12)
    (a b c d : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {a, b, c, d}) (hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hadj : G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d)
    (hA : ∀ y ∈ ({a, b, c, d} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 7 x₀))
    (hx : l.getD 1 x₀ = x₀) : False := by
  exact b24_c11 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm a b c d hR hd hadj hA hx
-- <</B24.C11>>

-- <<B25>>
lemma b25_hx0 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V}
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v) : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v := by
  intro v hv
  by_contra hlt
  push Not at hlt
  have hlen : 1 < (degreeSequence G).length := by
    simp only [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hsorted : (degreeSequence G).Pairwise (· ≤ ·) := by
    simp [degreeSequence]
  have hb : secondSmallestDegree G = (degreeSequence G)[1] := by
    unfold secondSmallestDegree
    rw [List.getD_eq_getElem _ _ hlen]
  -- filter of values < σ has length ≤ 1
  have hle1 : ((degreeSequence G).filter (fun d => decide (d < secondSmallestDegree G))).length ≤ 1 := by
    rcases hds : degreeSequence G with _ | ⟨a, _ | ⟨b, tail⟩⟩
    · simp [hds] at hlen
    · simp [hds] at hlen
    · have hbb : secondSmallestDegree G = b := by
        simp [secondSmallestDegree, hds]
      rw [hds] at hsorted
      have ht : ∀ t ∈ tail, b ≤ t := by
        intro t ht
        exact (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1 t ht
      rw [hbb]
      simp only [List.filter_cons]
      have : tail.filter (fun d => decide (d < b)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro t htt; have := ht t htt; simp; omega
      simp only [this]
      by_cases h1 : a < b <;> simp [h1]
  have hcnt : 2 ≤ (Finset.univ.filter (fun w => G.degree w < secondSmallestDegree G)).card := by
    have h2 : ({x₀, v} : Finset V) ⊆ Finset.univ.filter (fun w => G.degree w < secondSmallestDegree G) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact lt_of_le_of_lt (hmin v) hlt
      · exact hlt
    have := Finset.card_le_card h2
    rwa [Finset.card_pair (Ne.symm hv)] at this
  have heq : ((degreeSequence G).filter (fun d => decide (d < secondSmallestDegree G))).length
      = (Finset.univ.filter (fun w => G.degree w < secondSmallestDegree G)).card := by
    have hm : (degreeSequence G : Multiset ℕ) = Finset.univ.val.map (fun w => G.degree w) := by
      simp [degreeSequence]
    have := congrArg (fun m : Multiset ℕ => (m.filter (fun d => d < secondSmallestDegree G)).card) hm
    simp only [Multiset.filter_map, Multiset.card_map] at this
    rw [Finset.card_def, Finset.filter_val]
    have h3 : (Multiset.filter (fun d => d < secondSmallestDegree G) (degreeSequence G : Multiset ℕ)).card
        = ((degreeSequence G).filter (fun d => decide (d < secondSmallestDegree G))).length := by
      simp [Multiset.filter_coe]
    rw [← h3]
    simpa [Function.comp_def] using this
  omega

lemma thm_D_all [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn1 : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V)
    (hn2 : Fintype.card V ≤ 2 * secondSmallestDegree G + 6) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨x₀, hx₀⟩ := G.exists_minimal_degree_vertex
  have hmin : ∀ v, G.degree x₀ ≤ G.degree v := fun v => by
    rw [← hx₀]; exact G.minDegree_le_degree v
  have hx0 := b25_hx0 (G := G) hmin
  have hδ := h11 hconn hH hn1
  rcases Cadre.exists_cadre hconn hH hn1 hmin with ham | ⟨l, hne, hnd, hch, hmem, hhd, hlast, hmax, hlt⟩
  · exact ham
  · exfalso
    have hmg := Cadre.m_ge hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hg3 := Cadre.R_ge3 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hrc := Cadre.R_card hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hcase : (Finset.univ.filter (fun t => t ∉ l)).card = 3 ∨
        (Finset.univ.filter (fun t => t ∉ l)).card = 4 := by omega
    rcases hcase with h3 | h4
    · obtain ⟨u, v, w, hR, huv, hvw, huw, h1, h2, h3'⟩ :=
        Cadre.R3 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt h3
      exact Cadre.K3 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw
        h1 h2 h3' (by omega)
    · rcases Cadre.R4 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt h4 with
        ⟨a, b, c, d, hR, hab, hac, had, hbc, hbd, hcd, h1, h2, h3, h4', h5, h6⟩ |
        ⟨z, z', a, b, hR, h1, h2, h3, h4', h5, h6, hzz, e1, e2, e3, e4⟩
      · exact Cadre.R4_clique hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt a b c d hR
          ⟨hab, hac, had, hbc, hbd, hcd⟩ ⟨h1, h2, h3, h4', h5, h6⟩ (by omega)
      · exact Cadre.R4_nonclique hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt z z' a b hR
          ⟨h1, h2, h3, h4', h5, h6⟩ hzz e1 e2 e3 e4 (by omega)
-- <</B25>>

end Aux

section Final
open SimpleGraph

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.H2 := by
  intro h1 h2 V _ _ _ G _ hconn hH hn hb
  classical
  by_cases hn6 : Fintype.card V ≤ 2 * secondSmallestDegree G + 6
  · exact thm_D_all hconn hb hH hn hn6
  · obtain ⟨x₀, hx₀⟩ := G.exists_minimal_degree_vertex
    have hle : G.minDegree ≤ secondSmallestDegree G := by
      have := deg_x0_le (G := G) (x₀ := x₀) (fun v => by rw [← hx₀]; exact G.minDegree_le_degree v)
      rwa [← hx₀] at this
    rcases hle.lt_or_eq with hlt | heq
    · exact h2 G hconn hH (by omega) hb hlt
    · exact h1 G hconn hH (by omega) hb heq

end Final

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1

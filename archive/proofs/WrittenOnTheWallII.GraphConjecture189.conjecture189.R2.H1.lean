import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2

open SimpleGraph

namespace H1Aux

open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A set closed under adjacency away from `c`, not containing `c`. -/
def Closed (G : SimpleGraph V) (c : V) (C : Finset V) : Prop :=
  c ∉ C ∧ ∀ v ∈ C, ∀ w, G.Adj v w → w ≠ c → w ∈ C

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

/-- H1.2b -/
lemma h12b [DecidableRel G.Adj] (hconn : G.Connected) {c : V} {C : Finset V}
    (hC : Closed G c C) (hne : C.Nonempty) : ∃ u ∈ C, G.Adj u c := by
  obtain ⟨u0, hu0⟩ := hne
  obtain ⟨p⟩ := hconn.preconnected u0 c
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (↑C : Set V) (by simpa using hu0)
    (by simpa using hC.1)
  have hs : d.snd = c := by
    by_contra h
    exact hd2 (by simpa using hC.2 d.fst (by simpa using hd1) d.snd d.adj h)
  exact ⟨d.fst, by simpa using hd1, hs ▸ d.adj⟩

/-- H1.2c -/
lemma h12c (hconn : G.Connected) {c : V} {C : Finset V} (hC : Closed G c C)
    {u w : V} (hu : u ∈ C) (hw : w ∉ C) (hwc : w ≠ c) :
    G.dist u w = G.dist u c + G.dist c w := by
  apply le_antisymm
  · have := hconn.dist_triangle (u := u) (v := c) (w := w)
    exact this
  · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u w
    obtain ⟨d, hdm, hd1, hd2⟩ := p.exists_boundary_dart (↑C : Set V) (by simpa using hu)
      (by simpa using hw)
    have hs : d.snd = c := by
      by_contra h
      exact hd2 (by simpa using hC.2 d.fst (by simpa using hd1) d.snd d.adj h)
    have hcs : c ∈ p.support := hs ▸ p.dart_snd_mem_support_of_mem_darts hdm
    have hsp := congrArg Walk.length (p.take_spec hcs)
    rw [Walk.length_append] at hsp
    have h1 : G.dist u c ≤ (p.takeUntil c hcs).length := SimpleGraph.dist_le _
    have h2 : G.dist c w ≤ (p.dropUntil c hcs).length := SimpleGraph.dist_le _
    omega

/-- H1.2d -/
lemma h12d (hconn : G.Connected) {c : V} {C C' : Finset V} (hC : Closed G c C)
    (hC' : Closed G c C') (hd : Disjoint C C') {u z : V} (hu : u ∈ C) (hz : z ∈ C')
    (hu' : G.Adj u c) (hz' : G.Adj z c) : G.dist u z = 2 := by
  have hzc : z ≠ c := fun h => hC'.1 (h ▸ hz)
  have hnadj : ¬ G.Adj u z := fun h =>
    Finset.disjoint_left.mp hd (hC.2 u hu z h hzc) hz
  have hne : z ≠ u := fun h => Finset.disjoint_left.mp hd hu (h ▸ hz)
  exact dist_two hconn hu' hz'.symm hnadj hne

/-- H1.3a: n ≤ 3σ+1 -/
lemma h13a [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) {c : V} {C₁ C₂ : Finset V}
    (h1 : Closed G c C₁) (h2 : Closed G c C₂) (hd : Disjoint C₁ C₂)
    (hn1 : C₁.Nonempty) (hn2 : C₂.Nonempty) :
    Fintype.card V ≤ 3 * secondSmallestDegree G + 1 := by
  classical
  obtain ⟨u1, hu1, hu1c⟩ := h12b hconn h1 hn1
  obtain ⟨u2, hu2, hu2c⟩ := h12b hconn h2 hn2
  have hd1 : G.dist u1 c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu1c
  have hd2 : G.dist u2 c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu2c
  set S0 := Finset.univ.filter (fun w => Even (G.dist c w)) with hS0
  set S1 := (Finset.univ.filter (fun w => Even (G.dist u1 w))).erase u1 with hS1
  set S2 := (Finset.univ.filter (fun w => Even (G.dist u2 w))).erase u2 with hS2
  have hcov : (Finset.univ : Finset V) ⊆ S0 ∪ S1 ∪ S2 := by
    intro w _
    by_cases hw : Even (G.dist c w)
    · simp [hS0, hw]
    · have hwc : w ≠ c := by rintro rfl; simp at hw
      by_cases hw2 : w ∈ C₂
      · have hw1 : w ∉ C₁ := Finset.disjoint_right.mp hd hw2
        have h3 := h12c hconn h1 hu1 hw1 hwc
        have hne : w ≠ u1 := fun h => hw1 (h ▸ hu1)
        have hev : Even (G.dist u1 w) := by
          rw [Nat.even_iff]; rw [Nat.even_iff] at hw; omega
        simp [hS1, hne, hev]
      · have h3 := h12c hconn h2 hu2 hw2 hwc
        have hne : w ≠ u2 := fun h => hw2 (h ▸ hu2)
        have hev : Even (G.dist u2 w) := by
          rw [Nat.even_iff]; rw [Nat.even_iff] at hw; omega
        simp [hS2, hne, hev]
  have hc := Finset.card_le_card hcov
  have hu := Finset.card_union_le (S0 ∪ S1) S2
  have hu' := Finset.card_union_le S0 S1
  rw [Finset.card_univ] at hc
  have e0 : S0.card = distEven G c := rfl
  have e1 : S1.card = distEven G u1 - 1 := by
    rw [hS1, Finset.card_erase_of_mem (by simp)]; rfl
  have e2 : S2.card = distEven G u2 - 1 := by
    rw [hS2, Finset.card_erase_of_mem (by simp)]; rfl
  have := hH c
  have := hH u1
  have := hH u2
  have : 1 ≤ distEven G u1 := by
    unfold distEven
    exact Finset.card_pos.mpr ⟨u1, by simp⟩
  have : 1 ≤ distEven G u2 := by
    unfold distEven
    exact Finset.card_pos.mpr ⟨u2, by simp⟩
  omega

/-- degree bound inside a closed set -/
lemma deg_le_card [DecidableRel G.Adj] {c : V} {C : Finset V} (hC : Closed G c C) {z : V}
    (hz : z ∈ C) : G.degree z ≤ C.card := by
  have hsub : G.neighborFinset z ⊆ insert c (C.erase z) := by
    intro w hw
    rw [mem_neighborFinset] at hw
    by_cases hwc : w = c
    · simp [hwc]
    · simp [hwc, hC.2 z hz w hw hwc, hw.ne.symm]
  have := Finset.card_le_card hsub
  rw [card_neighborFinset_eq_degree] at this
  have h2 := Finset.card_insert_le c (C.erase z)
  have h3 := Finset.card_erase_of_mem hz
  have : 1 ≤ C.card := Finset.card_pos.mpr ⟨z, hz⟩
  omega

/-- H1.4: sizes. -/
lemma h14 [Nontrivial V] [DecidableRel G.Adj] {c : V} {C : Finset V} (hC : Closed G c C)
    (hne : C.Nonempty) (hδ : ∀ v, 2 ≤ G.degree v) (x₀ : V)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v) :
    secondSmallestDegree G ≤ C.card := by
  obtain ⟨u, hu⟩ := hne
  have h2 : 2 ≤ C.card := by
    have h := deg_le_card hC hu
    have := hδ u
    have hsub : G.neighborFinset u ⊆ insert c (C.erase u) := by
      intro w hw
      rw [mem_neighborFinset] at hw
      by_cases hwc : w = c
      · simp [hwc]
      · simp [hwc, hC.2 u hu w hw hwc, hw.ne.symm]
    have h5 := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree] at h5
    have h6 := Finset.card_insert_le c (C.erase u)
    have h7 := Finset.card_erase_of_mem hu
    omega
  obtain ⟨z, hz, hzx⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) x₀
  exact (hx0 z hzx).trans (deg_le_card hC hz)

/-- closed neighbourhood inside a closed set -/
lemma cnbr_sub [DecidableRel G.Adj] {c : V} {C : Finset V} (hC : Closed G c C) {z : V}
    (hz : z ∈ C) : insert z (G.neighborFinset z) ⊆ insert c C := by
  intro w hw
  rw [Finset.mem_insert] at hw
  rcases hw with rfl | hw
  · simp [hz]
  · rw [mem_neighborFinset] at hw
    by_cases hwc : w = c
    · simp [hwc]
    · simp [hC.2 z hz w hw hwc]

/-- H1.5 (D2). -/
lemma h15 [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected) {c : V} {C : Finset V}
    (hC : Closed G c C) (x₀ : V) (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hcard : C.card ≤ 2 * secondSmallestDegree G) {p r : V} (hp : p ∈ C) (hr : r ∈ C)
    (hpx : p ≠ x₀) (hrx : r ≠ x₀) (hpr : p ≠ r) : G.dist p r ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have hdis : Disjoint (insert p (G.neighborFinset p)) (insert r (G.neighborFinset r)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have a1 : G.dist p w ≤ 1 := by
      rw [Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · simp
      · rw [mem_neighborFinset] at h1
        exact (SimpleGraph.dist_eq_one_iff_adj.mpr h1).le
    have a2 : G.dist w r ≤ 1 := by
      rw [Finset.mem_insert] at h2
      rcases h2 with rfl | h2
      · simp
      · rw [mem_neighborFinset] at h2
        exact (SimpleGraph.dist_eq_one_iff_adj.mpr h2.symm).le
    have := hconn.dist_triangle (u := p) (v := w) (w := r)
    omega
  have hsub : insert p (G.neighborFinset p) ∪ insert r (G.neighborFinset r) ⊆ insert c C :=
    Finset.union_subset (cnbr_sub hC hp) (cnbr_sub hC hr)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at h1
  have e1 : (insert p (G.neighborFinset p)).card = G.degree p + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
  have e2 : (insert r (G.neighborFinset r)).card = G.degree r + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
  have := Finset.card_insert_le c C
  have := hx0 p hpx
  have := hx0 r hrx
  omega

/-- H1.6 (minimal side). -/
lemma h16 [Nontrivial V] [DecidableRel G.Adj] {c : V} {C : Finset V} (hC : Closed G c C)
    (x₀ : V) (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hcard : C.card = secondSmallestDegree G) (hx : x₀ ∉ C) : ∀ v ∈ C, G.Adj v c := by
  intro v hv
  have hvx : v ≠ x₀ := fun h => hx (h ▸ hv)
  have hsub : insert c (C.erase v) ⊆ G.neighborFinset v ∨ True := Or.inr trivial
  have hsub2 : G.neighborFinset v ⊆ insert c (C.erase v) := by
    intro w hw
    rw [mem_neighborFinset] at hw
    by_cases hwc : w = c
    · simp [hwc]
    · simp [hwc, hC.2 v hv w hw hwc, hw.ne.symm]
  have hdeg := hx0 v hvx
  have hcv : 1 ≤ C.card := Finset.card_pos.mpr ⟨v, hv⟩
  have hcard2 : (insert c (C.erase v)).card ≤ (G.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]
    have h2 := Finset.card_insert_of_notMem (s := C.erase v) (a := c)
      (fun h => hC.1 (Finset.mem_of_mem_erase h))
    have h3 := Finset.card_erase_of_mem hv
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub2 hcard2
  have : c ∈ G.neighborFinset v := by rw [heq]; simp
  simpa [mem_neighborFinset] using this

/-- H1.7 (limit case). -/
lemma h17 [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) {c : V} {C C' : Finset V}
    (hC : Closed G c C) (hC' : Closed G c C') (hd : Disjoint C C')
    (hn' : C'.Nonempty) (x₀ : V) (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v)
    (hcov : ∀ v, v = c ∨ v ∈ C ∨ v ∈ C')
    (hCc : C.card = 2 * secondSmallestDegree G) (hC'c : C'.card = secondSmallestDegree G)
    {v : V} (hv : v ∈ C) (hvc : G.Adj v c) (hvx : v ≠ x₀) :
    G.degree v ≠ secondSmallestDegree G := by
  classical
  intro hdeg
  have hσ := sigma_ge (G := G) hδ
  set σ := secondSmallestDegree G with hσdef
  set U := C.filter (fun w => ¬ (w = v ∨ G.Adj v w)) with hU
  have hUcard : σ ≤ U.card := by
    have hsub : C.filter (fun w => w = v ∨ G.Adj v w) ⊆
        insert v ((G.neighborFinset v).erase c) := by
      intro w hw
      simp only [Finset.mem_filter] at hw
      rcases hw.2 with rfl | h
      · simp
      · have hwc : w ≠ c := fun h' => hC.1 (h' ▸ hw.1)
        simp [mem_neighborFinset, h, hwc]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le v ((G.neighborFinset v).erase c)
    have h3 := Finset.card_erase_of_mem (s := G.neighborFinset v) (a := c)
      (by simpa [mem_neighborFinset] using hvc)
    rw [card_neighborFinset_eq_degree] at h3
    have h4 : (C.filter (fun w => w = v ∨ G.Adj v w)).card + U.card = C.card :=
      Finset.card_filter_add_card_filter_not _
    omega
  have hxne : ∀ w ∈ U, w ≠ x₀ → G.dist v w = 2 := by
    intro w hw hwx
    simp only [hU, Finset.mem_filter, not_or] at hw
    have hle := h15 hconn hC x₀ hx0 (by omega) hv hw.1 hvx hwx (Ne.symm hw.2.1)
    have h0 : G.dist v w ≠ 0 := fun h => hw.2.1 (hconn.dist_eq_zero_iff.mp h).symm
    have h1 : G.dist v w ≠ 1 := fun h => hw.2.2 (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  set A := C'.filter (fun z => G.Adj z c) with hA
  have hAd : ∀ z ∈ A, G.dist v z = 2 := by
    intro z hz
    simp only [hA, Finset.mem_filter] at hz
    exact h12d hconn hC hC' hd hv hz.1 hvc hz.2
  set T := U.erase x₀ ∪ A with hT
  have hTsub : T ⊆ ((Finset.univ.filter (fun w => Even (G.dist v w))).erase v) := by
    intro w hw
    rw [hT, Finset.mem_union] at hw
    rcases hw with hw | hw
    · rw [Finset.mem_erase] at hw
      have := hxne w hw.2 hw.1
      have hwv : w ≠ v := by
        have := (Finset.mem_filter.mp hw.2).2
        intro h; exact this (Or.inl h)
      simp [hwv, this]
    · have := hAd w hw
      have hwv : w ≠ v := by
        have hw' := (Finset.mem_filter.mp hw).1
        intro h; exact Finset.disjoint_left.mp hd hv (h ▸ hw')
      simp [hwv, this]
  have hTd : Disjoint (U.erase x₀) A := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp (Finset.mem_of_mem_erase h1)).1
      (Finset.mem_filter.mp h2).1
  have hcT := Finset.card_le_card hTsub
  rw [Finset.card_union_of_disjoint hTd] at hcT
  have hE := hH v
  have hEc : ((Finset.univ.filter (fun w => Even (G.dist v w))).erase v).card = distEven G v - 1 := by
    rw [Finset.card_erase_of_mem (by simp)]; rfl
  have hE1 : 1 ≤ distEven G v := by
    unfold distEven; exact Finset.card_pos.mpr ⟨v, by simp⟩
  have hUe : U.card ≤ (U.erase x₀).card + 1 := by
    have := Finset.pred_card_le_card_erase (s := U) (a := x₀)
    omega
  by_cases hx : x₀ ∈ C
  · have hx' : x₀ ∉ C' := fun h => Finset.disjoint_left.mp hd hx h
    have hAc : A.card = σ := by
      have : A = C' := by
        rw [hA]
        exact Finset.filter_true_of_mem (fun z hz => h16 hC' x₀ hx0 hC'c hx' z hz)
      rw [this, hC'c]
    omega
  · have hx' : x₀ ∈ C → False := hx
    obtain ⟨z, hz, hzc⟩ := h12b hconn hC' hn'
    have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨z, by simp [hA, hz, hzc]⟩
    have hUx : (U.erase x₀).card = U.card := by
      rw [Finset.erase_eq_of_notMem]
      intro h; exact hx (Finset.mem_filter.mp h).1
    omega

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

/-- Counting step H1.10-H1.11 on abstract index data. -/
lemma side [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) (x₀ : V)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v) (hδ : ∀ v, 2 ≤ G.degree v)
    {c : V} {D D' : Finset V} (hD : Closed G c D) (hD' : Closed G c D') (hd : Disjoint D D')
    (hn' : D'.Nonempty) (hcov : ∀ v, v = c ∨ v ∈ D ∨ v ∈ D')
    (g : ℕ → V) (m κ : ℕ) (hκ0 : 0 < κ) (hκm : κ < m) (hgc : g κ = c)
    (hinj : ∀ i < m, ∀ j < m, g i = g j → i = j)
    (hpre : ∀ i < κ, g i ∈ D) (hsuf : ∀ i, κ < i → i < m → g i ∉ D)
    (hdeg : secondSmallestDegree G ≤ G.degree (g 0) ∧ G.degree (g 0) ≤
      ((Finset.range (m - 1)).filter (fun j => G.Adj (g 0) (g (j + 1)))).card)
    (hF5 : ∀ y, (∀ i < m, g i ≠ y) → ∀ j < m, G.Adj y (g j) → 0 < j ∧ ¬ G.Adj (g 0) (g (j + 1)))
    {y : V} (hy : y ∈ D) (hyl : ∀ i < m, g i ≠ y) (hyx : y ≠ x₀) : False := by
  classical
  set σ := secondSmallestDegree G with hσ
  have hyne : D.Nonempty := ⟨y, hy⟩
  have h13 := h13a hconn hH hD hD' hd hyne hn'
  have hcardV : Fintype.card V = D.card + D'.card + 1 := by
    have : (Finset.univ : Finset V) = insert c (D ∪ D') := by
      ext v; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, true_iff]
      exact hcov v
    rw [← Finset.card_univ, this, Finset.card_insert_of_notMem
      (by simp [hD.1, hD'.1]), Finset.card_union_of_disjoint hd]
  have hD'ge := h14 hD' hn' hδ x₀ hx0
  have hDge := h14 hD hyne hδ x₀ hx0
  have hDle : D.card ≤ 2 * σ := by omega
  set R := D.filter (fun w => ∀ i < m, g i ≠ w) with hR
  have hyR : y ∈ R := Finset.mem_filter.mpr ⟨hy, hyl⟩
  set P := (Finset.range κ).image g with hP
  have hPD : P ⊆ D := by
    intro w hw
    simp only [hP, Finset.mem_image, Finset.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    exact hpre i hi
  have hPcard : P.card = κ := by
    rw [hP, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hinj i (by omega) j (by omega) hij
  have hPR : Disjoint P R := by
    rw [Finset.disjoint_left]
    intro w hw hwR
    simp only [hP, Finset.mem_image, Finset.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    simp only [hR, Finset.mem_filter] at hwR
    exact hwR.2 i (by omega) rfl
  have hDcard : κ + R.card ≤ D.card := by
    have := Finset.card_union_of_disjoint hPR
    have h2 : P ∪ R ⊆ D := Finset.union_subset hPD (Finset.filter_subset _ _)
    have := Finset.card_le_card h2
    omega
  have ha : g 0 ∈ D := hpre 0 hκ0
  set I₁ := (Finset.range (m - 1)).filter (fun j => G.Adj (g 0) (g (j + 1))) with hI₁
  have hI₁sub : I₁ ⊆ Finset.range κ := by
    intro j hj
    simp only [hI₁, Finset.mem_filter, Finset.mem_range] at hj ⊢
    by_contra hjk
    have hgj : g (j + 1) ∉ D := hsuf (j + 1) (by omega) (by omega)
    have hgc' : g (j + 1) = c := by
      by_contra hne
      exact hgj (hD.2 _ ha _ hj.2 hne)
    have := hinj (j + 1) (by omega) κ hκm (hgc'.trans hgc.symm)
    omega
  set J' := (Finset.range κ).filter (fun j => 1 ≤ j ∧ G.Adj y (g j)) with hJ'
  have hdisj : Disjoint I₁ J' := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [hI₁, hJ', Finset.mem_filter, Finset.mem_range] at h1 h2
    exact (hF5 y hyl j (by omega) h2.2.2).2 h1.2
  have hIJ : I₁.card + J'.card ≤ κ := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have : I₁ ∪ J' ⊆ Finset.range κ :=
      Finset.union_subset hI₁sub (Finset.filter_subset _ _)
    simpa using Finset.card_le_card this
  set B : Finset V := if G.Adj y c then {c} else ∅ with hB
  have hNsub : G.neighborFinset y ⊆ (J'.image g ∪ B) ∪ R.erase y := by
    intro w hw
    rw [mem_neighborFinset] at hw
    by_cases hwc : w = c
    · subst hwc
      simp [hB, hw]
    · have hwD : w ∈ D := hD.2 y hy w hw hwc
      by_cases hex : ∃ i < m, g i = w
      · obtain ⟨i, him, rfl⟩ := hex
        have hik : i < κ := by
          by_contra hik
          rcases Nat.lt_or_ge κ i with h | h
          · exact hsuf i h him hwD
          · have : i = κ := by omega
            subst this; exact hwc hgc
        have h0 := (hF5 y hyl i him hw).1
        simp only [Finset.mem_union, Finset.mem_image, hJ', Finset.mem_filter, Finset.mem_range]
        exact Or.inl (Or.inl ⟨i, ⟨hik, h0, hw⟩, rfl⟩)
      · push Not at hex
        simp only [Finset.mem_union, Finset.mem_erase, hR, Finset.mem_filter]
        exact Or.inr ⟨hw.ne.symm, hwD, hex⟩
  have hdy : G.degree y ≤ J'.card + B.card + (R.card - 1) := by
    have h1 := Finset.card_le_card hNsub
    rw [card_neighborFinset_eq_degree] at h1
    have h2 := Finset.card_union_le (J'.image g ∪ B) (R.erase y)
    have h3 := Finset.card_union_le (J'.image g) B
    have h4 := Finset.card_image_le (s := J') (f := g)
    have h5 := Finset.card_erase_of_mem hyR
    omega
  have hBc : B.card ≤ 1 := by
    simp only [hB]; split_ifs <;> simp
  have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨y, hyR⟩
  have hdyx := hx0 y hyx
  have hsum : G.degree (g 0) + G.degree y ≤ D.card - 1 + B.card := by
    have := hdeg.2
    omega
  have hBpos : B.card = 1 := by omega
  have hyc : G.Adj y c := by
    by_contra h
    simp [hB, h] at hBpos
  have hdy2 : G.degree y = σ := by omega
  have hD'c : D'.card = σ := by omega
  have hDc : D.card = 2 * σ := by omega
  exact h17 hconn hH hD hD' hd hn' x₀ hx0 hδ hcov hDc hD'c hy hyc hyx hdy2

/-- `side` applied to a list. -/
lemma side_list [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) (x₀ : V)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v) (hδ : ∀ v, 2 ≤ G.degree v)
    {c : V} {D D' : Finset V} (hD : Closed G c D) (hD' : Closed G c D') (hd : Disjoint D D')
    (hn' : D'.Nonempty) (hcov : ∀ v, v = c ∨ v ∈ D ∨ v ∈ D')
    (l : List V) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj) (hx : x₀ ∈ l)
    (h1h : l.head hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (κ : ℕ) (hκ0 : 0 < κ) (hκm : κ < l.length)
    (hgc : l.getD κ x₀ = c) (hpre : ∀ i < κ, l.getD i x₀ ∈ D)
    (hsuf : ∀ i, κ < i → i < l.length → l.getD i x₀ ∉ D) : ∀ y ∈ D, y ∈ l := by
  intro y hy
  by_contra hyl
  have hmax' : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') →
      l'.length ≤ l.length := fun l' a b hsub => hmax l' a b (hsub x₀ hx)
  obtain ⟨-, -, -, -, h5, -⟩ := lemma4x hconn l hne hnd hch hmax' hlt (by omega)
  have hgd : ∀ i d (hi : i < l.length), l.getD i d = l[i]'hi :=
    fun i d hi => List.getD_eq_getElem _ _ hi
  have hhead : l.head hne = l.getD 0 x₀ := by
    rw [hgd 0 x₀ (by omega)]
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have hyx : y ≠ x₀ := fun h => hyl (h ▸ hx)
  refine side hconn hH x₀ hx0 hδ hD hD' hd hn' hcov (fun i => l.getD i x₀) l.length κ hκ0 hκm
    hgc ?_ hpre hsuf ?_ ?_ hy ?_ hyx
  · intro i hi j hj hij
    simp only [hgd i x₀ hi, hgd j x₀ hj] at hij
    exact (hnd.getElem_inj_iff).mp hij
  · refine ⟨?_, ?_⟩
    · rw [← hhead]; exact hx0 _ h1h
    · rw [← hhead]
      refine h5.trans (le_of_eq ?_)
      congr 1
      apply Finset.filter_congr
      intro j hj
      simp only [Finset.mem_range] at hj
      rw [hgd (j + 1) _ (by omega), hgd (j + 1) x₀ (by omega), hhead]
  · intro y' hy' j hj hadj
    have hy'l : y' ∉ l := by
      intro hmem
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
      exact hy' i hi (by rw [hgd i x₀ hi])
    have hadj' : G.Adj y' (l.getD j y') := by
      have hadj2 : G.Adj y' (l.getD j x₀) := hadj
      rw [hgd j x₀ hj] at hadj2
      rw [hgd j y' hj]
      exact hadj2
    obtain ⟨h0, hj1, -, -, h5', -⟩ := lemma5abx hconn l hne hnd hch hmax' y' hy'l j hj hadj'
    refine ⟨h0, ?_⟩
    show ¬ G.Adj (l.getD 0 x₀) (l.getD (j + 1) x₀)
    rw [← hhead, hgd (j + 1) x₀ hj1, ← hgd (j + 1) y' hj1]
    exact h5'
  · intro i hi
    rw [hgd i x₀ hi]
    exact fun h => hyl (h ▸ List.getElem_mem hi)

/-- Both sides of `c` on the path lie in the same closed set. -/
lemma same_comp [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) (x₀ : V)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v) (hδ : ∀ v, 2 ≤ G.degree v)
    {c : V} {D D' : Finset V} (hD : Closed G c D) (hD' : Closed G c D') (hd : Disjoint D D')
    (hn' : D'.Nonempty) (hcov : ∀ v, v = c ∨ v ∈ D ∨ v ∈ D')
    (l : List V) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj) (hx : x₀ ∈ l)
    (h1h : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (κ : ℕ) (hκ0 : 0 < κ) (hκm : κ + 1 < l.length)
    (hgc : l.getD κ x₀ = c) (hall : ∀ i, i < l.length → i ≠ κ → l.getD i x₀ ∈ D) : False := by
  classical
  set σ := secondSmallestDegree G with hσ
  have hmax' : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') →
      l'.length ≤ l.length := fun l' a b hsub => hmax l' a b (hsub x₀ hx)
  have hgd : ∀ i d (hi : i < l.length), l.getD i d = l[i]'hi :=
    fun i d hi => List.getD_eq_getElem _ _ hi
  have hm2 : 2 ≤ l.length := by omega
  obtain ⟨-, -, h3, h4, h5, h6⟩ := lemma4x hconn l hne hnd hch hmax' hlt hm2
  have hda := hx0 _ h1h
  have hdb := hx0 _ hlast
  have hhead : l.head hne = l.getD 0 x₀ := by
    rw [hgd 0 x₀ (by omega)]
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have haD : l.head hne ∈ D := by rw [hhead]; exact hall 0 (by omega) (by omega)
  have hDne : D.Nonempty := ⟨_, haD⟩
  have h13 := h13a hconn hH hD hD' hd hDne hn'
  have hcardV : Fintype.card V = D.card + D'.card + 1 := by
    have : (Finset.univ : Finset V) = insert c (D ∪ D') := by
      ext v; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, true_iff]
      exact hcov v
    rw [← Finset.card_univ, this, Finset.card_insert_of_notMem
      (by simp [hD.1, hD'.1]), Finset.card_union_of_disjoint hd]
  have hD'ge := h14 hD' hn' hδ x₀ hx0
  have hsubl : l.toFinset ⊆ insert c D := by
    intro v hv
    rw [List.mem_toFinset] at hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    by_cases hik : i = κ
    · subst hik; rw [← hgd i x₀ hi, hgc]; simp
    · rw [← hgd i x₀ hi]; exact Finset.mem_insert_of_mem (hall i hi hik)
  have hcl := Finset.card_le_card hsubl
  rw [List.toFinset_card_of_nodup hnd] at hcl
  have hci := Finset.card_insert_le c D
  have hDc : D.card = 2 * σ := by omega
  have hD'c : D'.card = σ := by omega
  have hdega : G.degree (l.head hne) = σ := by omega
  set I₁ := (Finset.range (l.length - 1)).filter
    (fun j => G.Adj (l.head hne) (l.getD (j + 1) (l.head hne))) with hI₁
  set Im := (Finset.range (l.length - 1)).filter
    (fun j => G.Adj (l.getD j (l.head hne)) (l.getLast hne)) with hIm
  have hdis : Disjoint I₁ Im := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [hI₁, hIm, Finset.mem_filter, Finset.mem_range] at h1 h2
    exact h4 j (by omega) h1.2 h2.2
  have hunion : I₁ ∪ Im = Finset.range (l.length - 1) := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · rw [Finset.card_union_of_disjoint hdis, Finset.card_range]
      omega
  obtain ⟨u, hu, huc⟩ := h12b hconn hD' hn'
  have hul : u ∉ l := by
    intro hmem
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
    by_cases hik : i = κ
    · subst hik
      have : l[i] = c := by rw [← hgd i x₀ hi]; exact hgc
      exact hD'.1 (this ▸ hu)
    · have := hall i hi hik
      rw [hgd i x₀ hi] at this
      exact Finset.disjoint_left.mp hd this hu
  have hadj : G.Adj u (l.getD κ u) := by
    rw [hgd κ u (by omega), ← hgd κ x₀ (by omega), hgc]; exact huc
  obtain ⟨hk0, -, -, -, -, h6'⟩ := lemma5abx hconn l hne hnd hch hmax' u hul κ (by omega) hadj
  have hj : κ - 1 ∈ I₁ ∪ Im := by rw [hunion, Finset.mem_range]; omega
  have hjI : κ - 1 ∈ I₁ := by
    rcases Finset.mem_union.mp hj with h | h
    · exact h
    · exfalso
      simp only [hIm, Finset.mem_filter] at h
      apply h6'
      rw [hgd (κ - 1) u (by omega)]
      have := h.2
      rw [hgd (κ - 1) _ (by omega)] at this
      exact this.symm
  simp only [hI₁, Finset.mem_filter] at hjI
  have hac : G.Adj (l.head hne) c := by
    have := hjI.2
    rw [hgd (κ - 1 + 1) _ (by omega)] at this
    have e : κ - 1 + 1 = κ := by omega
    simp only [e] at this
    rw [← hgd κ x₀ (by omega), hgc] at this
    exact this
  exact h17 hconn hH hD hD' hd hn' x₀ hx0 hδ hcov hDc hD'c haD hac h1h hdega

/-- Walking along a chain inside a closed set (upward). -/
lemma seg_up {c : V} {D : Finset V} (hD : Closed G c D) (g : ℕ → V) (m : ℕ)
    (hadj : ∀ i, i + 1 < m → G.Adj (g i) (g (i + 1))) (a : ℕ) :
    ∀ b, a ≤ b → b < m → (∀ i, a ≤ i → i ≤ b → g i ≠ c) → g a ∈ D → g b ∈ D := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _ _ h; exact h
  | succ b hab ih =>
    intro hb hnc ha
    have := ih (by omega) (fun i h1 h2 => hnc i h1 (by omega)) ha
    exact hD.2 _ this _ (hadj b (by omega)) (hnc (b + 1) (by omega) le_rfl)

/-- Walking along a chain inside a closed set (downward). -/
lemma seg_down {c : V} {D : Finset V} (hD : Closed G c D) (g : ℕ → V) (m : ℕ)
    (hadj : ∀ i, i + 1 < m → G.Adj (g i) (g (i + 1))) (d : ℕ) :
    ∀ a, a + d < m → (∀ i, a ≤ i → i ≤ a + d → g i ≠ c) → g (a + d) ∈ D → g a ∈ D := by
  induction d with
  | zero => intro a _ _ h; simpa using h
  | succ d ih =>
    intro a hb hnc hgb
    have h1 : g (a + 1) ∈ D := by
      refine ih (a + 1) (by omega) (fun i h1 h2 => hnc i (by omega) (by omega)) ?_
      have e : a + 1 + d = a + (d + 1) := by omega
      rw [e]; exact hgb
    exact hD.2 _ h1 _ (hadj a (by omega)).symm (hnc a le_rfl (by omega))

/-- Interior position of `c` with the first vertex in `Da`. -/
lemma core_gen [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) (x₀ : V)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v) (hδ : ∀ v, 2 ≤ G.degree v)
    {c : V} {Da Db : Finset V} (hDa : Closed G c Da) (hDb : Closed G c Db) (hd : Disjoint Da Db)
    (hna : Da.Nonempty) (hnb : Db.Nonempty) (hcov : ∀ v, v = c ∨ v ∈ Da ∨ v ∈ Db)
    (l : List V) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj) (hx : x₀ ∈ l)
    (h1h : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (κ : ℕ) (hκ0 : 0 < κ) (hκm : κ + 1 < l.length)
    (hgc : l.getD κ x₀ = c) (h0 : l.getD 0 x₀ ∈ Da) : False := by
  classical
  have hgd : ∀ i d (hi : i < l.length), l.getD i d = l[i]'hi :=
    fun i d hi => List.getD_eq_getElem _ _ hi
  have hadjg : ∀ i, i + 1 < l.length → G.Adj (l.getD i x₀) (l.getD (i + 1) x₀) := by
    intro i hi
    rw [hgd i x₀ (by omega), hgd (i + 1) x₀ hi]
    exact hch.getElem i hi
  have hinj : ∀ i, i < l.length → ∀ j, j < l.length → l.getD i x₀ = l.getD j x₀ → i = j := by
    intro i hi j hj h
    rw [hgd i x₀ hi, hgd j x₀ hj] at h
    exact (hnd.getElem_inj_iff).mp h
  have hnc : ∀ i, i < l.length → i ≠ κ → l.getD i x₀ ≠ c := by
    intro i hi hik h
    exact hik (hinj i hi κ (by omega) (h.trans hgc.symm))
  have hpre : ∀ i, i < κ → l.getD i x₀ ∈ Da := by
    intro i hi
    have := seg_up hDa (fun i => l.getD i x₀) l.length hadjg 0 i (by omega) (by omega)
      (fun j _ hj => hnc j (by omega) (by omega)) h0
    exact this
  have hlastc : l.getD (l.length - 1) x₀ ≠ c := hnc _ (by omega) (by omega)
  have hlg : l.getD (l.length - 1) x₀ = l.getLast hne := by
    rw [hgd _ x₀ (by omega)]; exact (List.getLast_eq_getElem _).symm
  by_cases hsame : l.getD (l.length - 1) x₀ ∈ Da
  · refine same_comp hconn hH x₀ hx0 hδ hDa hDb hd hnb hcov l hne hnd hch hx h1h hlast hmax hlt
      κ hκ0 hκm hgc ?_
    intro i hi hik
    rcases Nat.lt_or_ge i κ with h | h
    · exact hpre i h
    · have hk : κ < i := by omega
      obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le (show i ≤ l.length - 1 by omega)
      have := seg_down hDa (fun i => l.getD i x₀) l.length hadjg d i (by omega)
        (fun j hj1 hj2 => hnc j (by omega) (by omega)) (by rw [← hd']; exact hsame)
      exact this
  · have hsb : l.getD (l.length - 1) x₀ ∈ Db := by
      rcases hcov (l.getD (l.length - 1) x₀) with h | h | h
      · exact absurd h hlastc
      · exact absurd h hsame
      · exact h
    have hsuf : ∀ i, κ < i → i < l.length → l.getD i x₀ ∈ Db := by
      intro i hk hi
      obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le (show i ≤ l.length - 1 by omega)
      exact seg_down hDb (fun i => l.getD i x₀) l.length hadjg d i (by omega)
        (fun j hj1 hj2 => hnc j (by omega) (by omega)) (by rw [← hd']; exact hsb)
    have hA : ∀ y ∈ Da, y ∈ l :=
      side_list hconn hH x₀ hx0 hδ hDa hDb hd hnb hcov l hne hnd hch hx h1h hmax hlt κ hκ0
        (by omega) hgc hpre (fun i hk hi h => Finset.disjoint_left.mp hd h (hsuf i hk hi))
    -- reversed list
    have hrne : l.reverse ≠ [] := by simpa using hne
    have hrg : ∀ i, i < l.length → l.reverse.getD i x₀ = l.getD (l.length - 1 - i) x₀ := by
      intro i hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi), hgd _ x₀ (by omega)]
      simp [List.getElem_reverse]
    have hB : ∀ y ∈ Db, y ∈ l.reverse := by
      refine side_list hconn hH x₀ hx0 hδ hDb hDa hd.symm hna
        (fun v => by rcases hcov v with h | h | h <;> simp [h]) l.reverse hrne
        (List.nodup_reverse.mpr hnd) (chain_rev hch) (List.mem_reverse.mpr hx) ?_ ?_ ?_
        (l.length - 1 - κ) (by omega) (by simp; omega) ?_ ?_ ?_
      · rw [List.head_reverse]; exact hlast
      · intro l' a b c'; rw [List.length_reverse]; exact hmax l' a b c'
      · simpa using hlt
      · rw [hrg _ (by omega)]
        have : l.length - 1 - (l.length - 1 - κ) = κ := by omega
        rw [this]; exact hgc
      · intro i hi
        rw [hrg i (by omega)]
        exact hsuf _ (by omega) (by omega)
      · intro i hk hi h
        rw [List.length_reverse] at hi
        rw [hrg i hi] at h
        have : l.getD (l.length - 1 - i) x₀ ∈ Da := hpre _ (by omega)
        exact Finset.disjoint_left.mp hd this h
    have huniv : (Finset.univ : Finset V) ⊆ l.toFinset := by
      intro v _
      rw [List.mem_toFinset]
      rcases hcov v with h | h | h
      · rw [h, ← hgc, hgd κ x₀ (by omega)]; exact List.getElem_mem _
      · exact hA v h
      · exact List.mem_reverse.mp (hB v h)
    have := Finset.card_le_card huniv
    rw [List.toFinset_card_of_nodup hnd, Finset.card_univ] at this
    omega

/-- H1.9-H1.11: the counting core. -/
lemma h1_core [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) (x₀ : V)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v) (hδ : ∀ v, 2 ≤ G.degree v)
    {c : V} {C₁ C₂ : Finset V} (h1 : Closed G c C₁) (h2 : Closed G c C₂)
    (hd : Disjoint C₁ C₂) (hn1 : C₁.Nonempty) (hn2 : C₂.Nonempty)
    (hcov : ∀ v, v = c ∨ v ∈ C₁ ∨ v ∈ C₂)
    (l : List V) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj) (hx : x₀ ∈ l)
    (h1h : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) : False := by
  classical
  set σ := secondSmallestDegree G with hσ
  have hmax' : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') →
      l'.length ≤ l.length := fun l' a b hsub => hmax l' a b (hsub x₀ hx)
  have hgd : ∀ i d (hi : i < l.length), l.getD i d = l[i]'hi :=
    fun i d hi => List.getD_eq_getElem _ _ hi
  have hadjg : ∀ i, i + 1 < l.length → G.Adj (l.getD i x₀) (l.getD (i + 1) x₀) := by
    intro i hi
    rw [hgd i x₀ (by omega), hgd (i + 1) x₀ hi]
    exact hch.getElem i hi
  have hinj : ∀ i, i < l.length → ∀ j, j < l.length → l.getD i x₀ = l.getD j x₀ → i = j := by
    intro i hi j hj h
    rw [hgd i x₀ hi, hgd j x₀ hj] at h
    exact (hnd.getElem_inj_iff).mp h
  have hm2 : 2 ≤ l.length := by
    by_contra h
    have h1' : l.length = 1 := by
      have := List.length_pos_iff.mpr hne; omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h1'
    simp at hx h1h
    exact h1h hx.symm
  obtain ⟨-, -, h3, -, -, -⟩ := lemma4x hconn l hne hnd hch hmax' hlt hm2
  have hda := hx0 _ h1h
  have hdb := hx0 _ hlast
  have h13 := h13a hconn hH h1 h2 hd hn1 hn2
  have hcardV : Fintype.card V = C₁.card + C₂.card + 1 := by
    have : (Finset.univ : Finset V) = insert c (C₁ ∪ C₂) := by
      ext v; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, true_iff]
      exact hcov v
    rw [← Finset.card_univ, this, Finset.card_insert_of_notMem
      (by simp [h1.1, h2.1]), Finset.card_union_of_disjoint hd]
  have hC1ge := h14 h1 hn1 hδ x₀ hx0
  have hC2ge := h14 h2 hn2 hδ x₀ hx0
  have hC1le : C₁.card ≤ 2 * σ := by omega
  have hC2le : C₂.card ≤ 2 * σ := by omega
  -- c lies on the path
  have hcl : c ∈ l := by
    by_contra hcl
    have hnc0 : ∀ i, i < l.length → l.getD i x₀ ≠ c := fun i hi h =>
      hcl (by rw [← h, hgd i x₀ hi]; exact List.getElem_mem _)
    have key : ∀ D : Finset V, Closed G c D → l.getD 0 x₀ ∈ D → D.card ≤ 2 * σ → False := by
      intro D hD h0 hDle
      have hsub : l.toFinset ⊆ D := by
        intro v hv
        rw [List.mem_toFinset] at hv
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
        rw [← hgd i x₀ hi]
        exact seg_up hD (fun i => l.getD i x₀) l.length hadjg 0 i (by omega) hi
          (fun j _ _ => hnc0 j (by omega)) h0
      have := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hnd] at this
      omega
    rcases hcov (l.getD 0 x₀) with h | h | h
    · exact hnc0 0 (by omega) h
    · exact key C₁ h1 h hC1le
    · exact key C₂ h2 h hC2le
  obtain ⟨κ, hκ, hκc⟩ := List.mem_iff_getElem.mp hcl
  have hgc : l.getD κ x₀ = c := by rw [hgd κ x₀ hκ]; exact hκc
  have hnc : ∀ i, i < l.length → i ≠ κ → l.getD i x₀ ≠ c := by
    intro i hi hik h
    exact hik (hinj i hi κ hκ (h.trans hgc.symm))
  -- the position of `c` is interior
  have hends : 0 < κ ∧ κ + 1 < l.length := by
    by_contra hnot
    have key : ∀ D D'' : Finset V, Closed G c D → Closed G c D'' → Disjoint D D'' →
        D''.Nonempty → (∀ i, i < l.length → i ≠ κ → l.getD i x₀ ∈ D) → False := by
      intro D D'' hD hD'' hdd hn'' hall
      obtain ⟨u, hu, huc⟩ := h12b hconn hD'' hn''
      have hul : u ∉ l := by
        intro hmem
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
        by_cases hik : i = κ
        · subst hik
          have : l[i] = c := hκc
          exact hD''.1 (this ▸ hu)
        · have := hall i hi hik
          rw [hgd i x₀ hi] at this
          exact Finset.disjoint_left.mp hdd this hu
      have hadj : G.Adj u (l.getD κ u) := by
        rw [hgd κ u hκ, ← hgd κ x₀ hκ, hgc]; exact huc
      obtain ⟨hk0, hk1, -⟩ := lemma5abx hconn l hne hnd hch hmax' u hul κ hκ hadj
      exact hnot ⟨hk0, hk1⟩
    have hk' : κ = 0 ∨ κ = l.length - 1 := by omega
    have hall_of : ∀ i0, i0 < l.length → i0 ≠ κ → (∀ i, i < l.length → i ≠ κ →
        (i0 ≤ i ∨ i ≤ i0) ∧ (∀ j, min i i0 ≤ j → j ≤ max i i0 → j ≠ κ)) →
        ∀ D, Closed G c D → l.getD i0 x₀ ∈ D → ∀ i, i < l.length → i ≠ κ → l.getD i x₀ ∈ D := by
      intro i0 hi0 hik0 hconv D hD h0 i hi hik
      obtain ⟨-, hrange⟩ := hconv i hi hik
      rcases Nat.le_total i0 i with h | h
      · exact seg_up hD (fun i => l.getD i x₀) l.length hadjg i0 i h hi
          (fun j hj1 hj2 => hnc j (by omega) (hrange j (by omega) (by omega))) h0
      · obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le h
        have := seg_down hD (fun i => l.getD i x₀) l.length hadjg d i (by omega)
          (fun j hj1 hj2 => hnc j (by omega) (hrange j (by omega) (by omega)))
          (by rw [← hd']; exact h0)
        exact this
    rcases hk' with hk | hk
    · have hi0 : (1 : ℕ) < l.length := by omega
      have hg1 : l.getD 1 x₀ ≠ c := hnc 1 hi0 (by omega)
      have hconv : ∀ i, i < l.length → i ≠ κ → (1 ≤ i ∨ i ≤ 1) ∧
          (∀ j, min i 1 ≤ j → j ≤ max i 1 → j ≠ κ) := by
        intro i hi hik
        refine ⟨by omega, fun j hj1 hj2 => ?_⟩
        have : 1 ≤ i := by omega
        simp only [min_eq_right this, max_eq_left this] at hj1 hj2
        omega
      rcases hcov (l.getD 1 x₀) with h | h | h
      · exact hg1 h
      · exact key C₁ C₂ h1 h2 hd hn2 (hall_of 1 hi0 (by omega) hconv C₁ h1 h)
      · exact key C₂ C₁ h2 h1 hd.symm hn1 (hall_of 1 hi0 (by omega) hconv C₂ h2 h)
    · have hi0 : (0 : ℕ) < l.length := by omega
      have hg1 : l.getD 0 x₀ ≠ c := hnc 0 hi0 (by omega)
      have hconv : ∀ i, i < l.length → i ≠ κ → (0 ≤ i ∨ i ≤ 0) ∧
          (∀ j, min i 0 ≤ j → j ≤ max i 0 → j ≠ κ) := by
        intro i hi hik
        refine ⟨by omega, fun j hj1 hj2 => ?_⟩
        simp only [min_eq_right (Nat.zero_le i), max_eq_left (Nat.zero_le i)] at hj1 hj2
        omega
      rcases hcov (l.getD 0 x₀) with h | h | h
      · exact hg1 h
      · exact key C₁ C₂ h1 h2 hd hn2 (hall_of 0 hi0 (by omega) hconv C₁ h1 h)
      · exact key C₂ C₁ h2 h1 hd.symm hn1 (hall_of 0 hi0 (by omega) hconv C₂ h2 h)
  obtain ⟨hκ0, hκm⟩ := hends
  have hg0 : l.getD 0 x₀ ≠ c := hnc 0 (by omega) (by omega)
  rcases hcov (l.getD 0 x₀) with h | h | h
  · exact hg0 h
  · exact core_gen hconn hH x₀ hx0 hδ h1 h2 hd hn1 hn2 hcov l hne hnd hch hx h1h hlast hmax hlt
      κ hκ0 hκm hgc h
  · exact core_gen hconn hH x₀ hx0 hδ h2 h1 hd.symm hn2 hn1
      (fun v => by rcases hcov v with h | h | h <;> simp [h]) l hne hnd hch hx h1h hlast hmax hlt
      κ hκ0 hκm hgc h

/-- Disconnected `G - c` gives two closed nonempty parts covering everything. -/
lemma split_parts [DecidableRel G.Adj] {c : V}
    (hdis : ¬ (G.induce {x | x ≠ c}).Connected) (hcard : 2 ≤ Fintype.card V) :
    ∃ C₁ C₂ : Finset V, Closed G c C₁ ∧ Closed G c C₂ ∧ Disjoint C₁ C₂ ∧ C₁.Nonempty ∧
      C₂.Nonempty ∧ ∀ v, v = c ∨ v ∈ C₁ ∨ v ∈ C₂ := by
  classical
  have hne : Nonempty {x : V | x ≠ c} := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
    by_cases h : a = c
    · exact ⟨⟨b, fun hb => hab (h.trans hb.symm)⟩⟩
    · exact ⟨⟨a, h⟩⟩
  have hpre : ¬ (G.induce {x : V | x ≠ c}).Preconnected := fun h => hdis ⟨h⟩ |>.elim
  have hpre' := hpre
  rw [SimpleGraph.Preconnected] at hpre'
  push Not at hpre'
  obtain ⟨a, b, hab⟩ := hpre'
  set R : V → Prop := fun v => ∃ h : v ≠ c, (G.induce {x : V | x ≠ c}).Reachable ⟨v, h⟩ a with hR
  have hRadj : ∀ v w, R v → G.Adj v w → w ≠ c → R w := by
    intro v w ⟨hv, hrv⟩ hvw hwc
    refine ⟨hwc, ?_⟩
    have : (G.induce {x : V | x ≠ c}).Adj ⟨w, hwc⟩ ⟨v, hv⟩ := by
      simpa using hvw.symm
    exact this.reachable.trans hrv
  refine ⟨Finset.univ.filter R, Finset.univ.filter (fun v => v ≠ c ∧ ¬ R v), ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ⟨a.1, ?_⟩, ⟨b.1, ?_⟩, ?_⟩
  · simp [hR]
  · intro v hv w hvw hwc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hRadj v w hv hvw hwc
  · simp
  · intro v hv w hvw hwc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    refine ⟨hwc, fun hw => hv.2 ?_⟩
    exact hRadj w v hw hvw.symm hv.1
  · rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2.2 h1
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hR]
    exact ⟨a.2, by simpa using Reachable.refl _⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hR]
    refine ⟨b.2, ?_⟩
    rintro ⟨h, hr⟩
    exact hab (by simpa using hr.symm)
  · intro v
    by_cases hv : v = c
    · exact Or.inl hv
    · by_cases hr : R v
      · exact Or.inr (Or.inl (by simpa using hr))
      · exact Or.inr (Or.inr (by simpa using ⟨hv, hr⟩))

end H1Aux

section Final
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2

theorem H1Aux.main {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V)
    (hc : ∃ c : V, ¬ (G.induce {x | x ≠ c}).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨c, hcdis⟩ := hc
  have hδ := H1Aux.h11 hconn hH hn
  obtain ⟨x₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun v : V => G.degree v)
    Finset.univ_nonempty
  have hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v := by
    intro v hv
    rcases degree_pair (G := G) x₀ v (Ne.symm hv) with h | h
    · exact h.trans (hmin v (Finset.mem_univ v))
    · exact h
  obtain ⟨C₁, C₂, h1, h2, hd, hn1, hn2, hcov⟩ := H1Aux.split_parts (G := G) hcdis
    (Nat.succ_le_of_lt Fintype.one_lt_card)
  by_cases hall : ∀ l : List V, l.Nodup → l.IsChain G.Adj → x₀ ∈ l → l.length < Fintype.card V
  · exfalso
    obtain ⟨l, hne, hnd, hch, hx, h1h, hlast, hmax⟩ := H1Aux.h18 hconn x₀ hδ hall
    exact H1Aux.h1_core hconn hH x₀ hx0 hδ h1 h2 hd hn1 hn2 hcov l hne hnd hch hx h1h hlast
      hmax (hall l hnd hch hx)
  · push Not at hall
    obtain ⟨l, hnd, hch, hx, hlen⟩ := hall
    have hne : l ≠ [] := List.ne_nil_of_mem hx
    exact ham_of_list l hne hnd hch (le_antisymm hnd.length_le_card hlen)

end Final

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.H1 := by
  intro V _ _ _ G _ hconn hH hn hc
  exact H1Aux.main G hconn hH hn hc


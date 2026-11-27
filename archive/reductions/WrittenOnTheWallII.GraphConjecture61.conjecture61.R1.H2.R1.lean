import OMAReductions.R_WrittenOnTheWallII_GraphConjecture61_conjecture61_R1

/-!
# Diameter four of Graffiti 61 by strong induction, and the vertex-deletion lemma

The parent step `H2` asks for `residue + ceil (diam / 3) ≤ f` for connected graphs with
`4 ≤ diam` and `indepNum + (diam + 3) / 4 < residue + ceil (diam / 3)`. This file proves the
case `diam = 4` outright (theorem D4: `residue + 2 ≤ f`), using two known facts about the
residue, and leaves the cases `diam ≥ 5` open as `H1` (`5 ≤ diam ≤ 15`) and `H2` (`16 ≤ diam`).

* `H3` is the theorem of Favaron, Maheo and Sacle: `residue ≤ indepNum`.
* `H4` says that deleting a vertex of maximum degree does not decrease the residue. It is the
  inequality `residue G ≤ residue (G - w)` proved on the way to `H3`.

Proof of D4: strong induction on the number of vertices. Let `w` have maximum degree and
suppose `f ≤ residue + 1`. Then `residue = indepNum`, `f = indepNum + 1`, and the two ends of a
geodesic of length four lie in every maximum independent set. Hence `w` lies outside some
maximum independent set, and `G - w` is disconnected (else the induction hypothesis or the
bound `indepNum + (diam + 3) / 4 ≤ f` gives the result). The components of `G - w` are one
big component `C` and pendant vertices `L` of `w`. If an end of the geodesic is pendant, an
edge exchange (`exists_two_switch`) lowers the residue below `indepNum`; otherwise both ends
lie in `C`, and induction on `C` plus isolated vertices (`residue_induce_isolated`) concludes.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture61_conjecture61_R1_H2_R1

open SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture61_conjecture61_R1 (isAcyclic_of_leaf_edges
  card_le_forest isAcyclic_induce_union dist_getVert_of_shortest edist_hom_le
  indepNum_add_le_forest residue_iso)

/-- The open step `H2` of the parent, restricted to `5 ≤ diam ≤ 15`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
    [DecidableRel G.Adj], G.Connected → (5 ≤ G.diam ∧ G.diam ≤ 15) →
    (G.indepNum : ℝ) + ((G.diam + 3) / 4 : ℕ) < (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ →
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ)

/-- The open step `H2` of the parent, restricted to `16 ≤ diam`. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
    [DecidableRel G.Adj], G.Connected → 16 ≤ G.diam →
    (G.indepNum : ℝ) + ((G.diam + 3) / 4 : ℕ) < (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ →
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ)

/-- Favaron, Maheo, Sacle (1991): the Havel-Hakimi residue is at most the independence number. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.residue ≤ G.indepNum

/-- Deleting a vertex of maximum degree from a graph with an edge does not decrease the
residue. -/
def H4 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (w : V),
    (∃ a b, G.Adj a b) → (∀ v, G.degree v ≤ G.degree w) →
    G.residue ≤ (G.induce {a | a ≠ w}).residue

section residue_seq

lemma sd_mergeSort (l : List ℕ) : (l.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) := by
  have h := List.pairwise_mergeSort (l := l) (le := fun a b => decide (a ≥ b))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
    (fun a b => by by_cases hab : a ≥ b <;> simp [hab]; omega)
  simpa using h

lemma sd_eq_of_perm {a b : List ℕ} (ha : a.Pairwise (· ≥ ·)) (hb : b.Pairwise (· ≥ ·))
    (h : a.Perm b) : a = b :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h2 h1) ha hb h

lemma mergeSort_append_zero (l : List ℕ) :
    (l ++ [0]).mergeSort (· ≥ ·) = l.mergeSort (· ≥ ·) ++ [0] := by
  apply sd_eq_of_perm (sd_mergeSort _)
  · rw [List.pairwise_append]
    refine ⟨sd_mergeSort l, List.pairwise_singleton _ _, ?_⟩
    intro a _ b hb
    simp only [List.mem_singleton] at hb
    omega
  · exact (List.mergeSort_perm _ _).trans (((List.mergeSort_perm l _).symm).append_right [0])

lemma hh_append_zero (d : ℕ) (r : List ℕ) (hd : d ≤ r.length) :
    havelHakimiStep (d :: (r ++ [0])) = havelHakimiStep (d :: r) ++ [0] := by
  simp only [havelHakimiStep, List.splitAt_eq, List.take_append_of_le_length hd,
    List.drop_append_of_le_length hd]
  rw [← List.append_assoc]
  exact mergeSort_append_zero _

lemma hh_head_le (d : ℕ) (r : List ℕ) (hs : (d :: r).Pairwise (· ≥ ·)) (hd : d ≤ r.length)
    (e : ℕ) (r' : List ℕ) (h : havelHakimiStep (d :: r) = e :: r') : e ≤ r'.length := by
  have hlen := havelHakimiStep_length_cons d r
  rw [h] at hlen
  simp only [List.length_cons] at hlen
  have hmem : e ∈ havelHakimiStep (d :: r) := by rw [h]; exact List.mem_cons_self
  have hle : ∀ x ∈ r, x ≤ d := fun x hx => (List.pairwise_cons.mp hs).1 x hx
  simp only [havelHakimiStep, List.splitAt_eq] at hmem
  have hmem' := (List.mergeSort_perm _ _).mem_iff.mp hmem
  rw [List.mem_append, List.mem_map] at hmem'
  rcases hmem' with ⟨a, ha, rfl⟩ | ha
  · have hr := List.mem_of_mem_take ha
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        simp at ha
      · exact h0
    have := hle a hr
    omega
  · have hr := List.mem_of_mem_drop ha
    have hl : 0 < (r.drop d).length := List.length_pos_of_mem ha
    rw [List.length_drop] at hl
    have := hle e hr
    omega

lemma residueAux_append_zero : ∀ (m : ℕ) (D : List ℕ), D.length = m → D.Pairwise (· ≥ ·) →
    (∀ d r, D = d :: r → d ≤ r.length) → residueAux (D ++ [0]) = residueAux D + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro D hm hs hinv
    match D with
    | [] => simp [residueAux]
    | 0 :: s =>
      simp only [List.cons_append, residueAux, List.length_append, List.length_singleton]
      omega
    | (d + 1) :: r =>
      have hd : d + 1 ≤ r.length := hinv _ _ rfl
      have hlen := havelHakimiStep_length_cons (d + 1) r
      have e1 : residueAux ((d + 1) :: (r ++ [0])) =
          residueAux (havelHakimiStep ((d + 1) :: (r ++ [0]))) := by
        rw [residueAux]
        intro h
        omega
      have e2 : residueAux ((d + 1) :: r) = residueAux (havelHakimiStep ((d + 1) :: r)) := by
        rw [residueAux]
        intro h
        omega
      rw [List.cons_append, e1, e2, hh_append_zero _ _ hd]
      have hsorted : (havelHakimiStep ((d + 1) :: r)).Pairwise (· ≥ ·) := by
        unfold havelHakimiStep
        exact sd_mergeSort _
      exact ih _ (by simp only [List.length_cons] at hm; omega) _ rfl hsorted
        (fun e r' h => hh_head_le (d + 1) r hs hd e r' h)

end residue_seq

section residue_lemmas

open Classical

variable {V : Type} [Fintype V]

/-- The residue depends on the degrees only. -/
lemma residue_congr_degree (G K : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel K.Adj]
    (h : ∀ v, G.degree v = K.degree v) : G.residue = K.residue := by
  unfold SimpleGraph.residue
  have : (Finset.univ.val.map fun v => G.degree v) = (Finset.univ.val.map fun v => K.degree v) :=
    Multiset.map_congr rfl (fun v _ => h v)
  rw [this]

open Finset in
lemma degree_induce_ne' (G : SimpleGraph V) (v : V) (a : {a : V // a ≠ v}) :
    (G.induce {a | a ≠ v}).degree a = G.degree a.1 - (if G.Adj v a.1 then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have heq :
      ((G.induce {a | a ≠ v}).neighborFinset a).map (Function.Embedding.subtype _) =
        (G.neighborFinset a.1).erase v := by
    ext b
    simp only [mem_map, mem_neighborFinset, Function.Embedding.subtype_apply, mem_erase,
      Subtype.exists, SimpleGraph.induce_adj, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, hca, rfl⟩; exact ⟨hc, hca⟩
    · rintro ⟨hbv, hba⟩; exact ⟨b, hbv, hba, rfl⟩
  rw [← Finset.card_map (Function.Embedding.subtype _), heq]
  by_cases hadj : G.Adj v a.1
  · rw [if_pos hadj, card_erase_of_mem (by rw [mem_neighborFinset]; exact hadj.symm)]
  · rw [if_neg hadj, Nat.sub_zero, erase_eq_of_notMem (by simpa [mem_neighborFinset, adj_comm] using hadj)]

/-- One isolated vertex adds one to the residue. -/
lemma residue_isolated_vertex (H : SimpleGraph V) [DecidableRel H.Adj] (s : V)
    (hs : ∀ b, ¬ H.Adj s b) :
    H.residue = (H.induce {a | a ≠ s}).residue + 1 := by
  have hdeg0 : H.degree s = 0 := by
    rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero]
    ext b
    simp [mem_neighborFinset, hs b]
  have hdegW : ∀ a : {a : V // a ≠ s}, (H.induce {a | a ≠ s}).degree a = H.degree a.1 := by
    intro a
    have h := degree_induce_ne' H s a
    rw [if_neg (hs a.1), Nat.sub_zero] at h
    convert h
  have h1 : (Finset.univ : Finset {a : V // a ≠ s}).val.map
        (fun a => (H.induce {a | a ≠ s}).degree a) =
      (Finset.univ.erase s).val.map (fun v => H.degree v) := by
    have hmap : (Finset.univ : Finset {a : V // a ≠ s}).map (Function.Embedding.subtype _) =
        Finset.univ.erase s := by
      ext b
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.subtype_apply,
        Finset.mem_erase, ne_eq, Subtype.exists, exists_prop, exists_eq_right, and_true]
    rw [← hmap, Finset.map_val, Multiset.map_map]
    exact Multiset.map_congr rfl (fun a _ => hdegW a)
  have h2 : (Finset.univ : Finset V).val = s ::ₘ (Finset.univ.erase s).val := by
    rw [Finset.erase_val, Multiset.cons_erase (Finset.mem_univ s)]
  have hM : (Finset.univ : Finset V).val.map (fun v => H.degree v) =
      (Finset.univ : Finset {a : V // a ≠ s}).val.map
        (fun a => (H.induce {a | a ≠ s}).degree a) + {0} := by
    rw [h2, Multiset.map_cons, hdeg0, h1, add_comm, Multiset.singleton_add]
  unfold residue
  rw [hM]
  generalize hM2 : (Finset.univ : Finset {a : V // a ≠ s}).val.map
        (fun a => (H.induce {a | a ≠ s}).degree a) = M2
  have hsort : (M2 + {0}).sort (· ≥ ·) = M2.sort (· ≥ ·) ++ [0] := by
    apply sd_eq_of_perm (Multiset.pairwise_sort _ _)
    · rw [List.pairwise_append]
      refine ⟨Multiset.pairwise_sort _ _, List.pairwise_singleton _ _, ?_⟩
      intro a _ b hb
      simp only [List.mem_singleton] at hb
      omega
    · apply Multiset.coe_eq_coe.mp
      rw [Multiset.sort_eq, ← Multiset.coe_add, Multiset.sort_eq]
      rfl
  rw [hsort]
  apply residueAux_append_zero _ _ rfl (Multiset.pairwise_sort _ _)
  intro d r hdr
  have hlen : (M2.sort (· ≥ ·)).length = Fintype.card {a : V // a ≠ s} := by
    rw [Multiset.length_sort, ← hM2, Multiset.card_map]
    exact Finset.card_univ
  have hmem : d ∈ M2 := by
    rw [← Multiset.mem_sort (· ≥ ·), hdr]
    exact List.mem_cons_self
  rw [← hM2, Multiset.mem_map] at hmem
  obtain ⟨a, _, ha⟩ := hmem
  have hlt := (H.induce {a | a ≠ s}).degree_lt_card_verts a
  rw [ha] at hlt
  rw [hdr] at hlen
  simp only [List.length_cons] at hlen
  have : Fintype.card ↥({a | a ≠ s} : Set V) = Fintype.card {a : V // a ≠ s} := rfl
  omega

lemma induce_erase_iso (G : SimpleGraph V) (s : Set V) (l : V) (hl : l ∈ s) :
    Nonempty (((G.induce s).induce {a | a ≠ (⟨l, hl⟩ : s)}) ≃g G.induce (s \ {l})) :=
  ⟨{ toFun := fun x => ⟨x.1.1, x.1.2, fun h => x.2 (Subtype.ext h)⟩
     invFun := fun y => ⟨⟨y.1, y.2.1⟩, fun h => y.2.2 (congrArg Subtype.val h)⟩
     left_inv := fun x => rfl
     right_inv := fun y => rfl
     map_rel_iff' := Iff.rfl }⟩

/-- One isolated vertex of an induced subgraph can be removed, adding one to the residue. -/
lemma residue_induce_erase_isolated (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) (l : V)
    (hl : l ∈ s) (hiso : ∀ b ∈ s, ¬ G.Adj l b) :
    (G.induce s).residue = (G.induce (s \ {l})).residue + 1 := by
  have h := residue_isolated_vertex (G.induce s) ⟨l, hl⟩ (fun b => hiso b.1 b.2)
  obtain ⟨e⟩ := induce_erase_iso G s l hl
  have h3 := residue_iso e
  rw [h]
  refine congrArg (· + 1) ?_
  convert h3.symm

/-- L4. Isolated vertices add one each to the residue. Remaining: iterate
`residue_induce_erase_isolated` over `L` (induction on `L`; the instance defeq checks between
the `Fintype` instances of the successive set differences time out and need `convert`). -/
lemma residue_induce_isolated (G : SimpleGraph V) [DecidableRel G.Adj] (s s' : Set V)
    (L : Finset V) (hL : (L : Set V) ⊆ s) (hiso : ∀ l ∈ L, ∀ b ∈ s, ¬ G.Adj l b)
    (hs' : s' = s \ (L : Set V)) :
    (G.induce s).residue = (G.induce s').residue + L.card := by
  induction L using Finset.induction_on generalizing s s' with
  | empty =>
    have e : s' = s := by rw [hs']; simp
    subst e
    simp
  | insert a L0 ha ih =>
    have haS : a ∈ s := hL (by simp)
    have h1 := residue_induce_erase_isolated G s a haS (hiso a (by simp))
    have h2 := ih (s \ {a}) ((s \ {a}) \ (L0 : Set V))
      (fun x hx => ⟨hL (by simp [hx]), by
        intro h; rw [Set.mem_singleton_iff] at h; subst h; exact ha hx⟩)
      (fun l hl b hb => hiso l (by simp [hl]) b hb.1) rfl
    have hset : s' = (s \ {a}) \ (L0 : Set V) := by
      rw [hs']; ext x; simp [and_assoc, and_comm, and_left_comm]
    subst hset
    rw [h1, Finset.card_insert_of_notMem ha, ← add_assoc]
    convert congrArg (· + 1) h2 using 3

end residue_lemmas

section indep_lemmas

open Classical

variable {V : Type} [Fintype V]

lemma indepNum_induce_le (G : SimpleGraph V) (s : Set V) :
    (G.induce s).indepNum ≤ G.indepNum := by
  obtain ⟨t, ht⟩ := (G.induce s).exists_isNIndepSet_indepNum
  have hind : G.IsIndepSet ((t.map (Function.Embedding.subtype _) : Finset V) : Set V) := by
    intro a ha b hb hab hadj
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Function.Embedding.coe_subtype] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ht.1 ha' hb' (fun h => hab (by rw [h])) hadj
  have := hind.card_le_indepNum
  rw [Finset.card_map, ht.2] at this
  exact this

/-- L6. A pendant vertex `l` at `w`. -/
lemma indepNum_pendant (G : SimpleGraph V) (w l : V) (hlw : G.Adj l w)
    (hl : ∀ c, G.Adj l c → c = w) :
    G.indepNum = (G.induce {a | a ≠ w ∧ a ≠ l}).indepNum + 1 := by
  apply le_antisymm
  · obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    have hind : G.IsIndepSet (I : Set V) := hI.1
    let p : V → Prop := fun a => a ∈ {a : V | a ≠ w ∧ a ≠ l}
    have hsub : (G.induce {a | a ≠ w ∧ a ≠ l}).IsIndepSet
        ((I.subtype p : Finset _) : Set _) := by
      intro a ha b hb hab hadj
      rw [Finset.mem_coe, Finset.mem_subtype] at ha hb
      exact hind (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
        (fun h => hab (Subtype.ext h)) hadj
    have h2 := hsub.card_le_indepNum
    rw [Finset.card_subtype] at h2
    have h3 : (I.filter (fun a => ¬ p a)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      have hwl : ∀ c, c ∈ I → ¬ p c → c = w ∨ c = l := by
        intro c _ hc
        simp only [p, Set.mem_setOf_eq, not_and_or, not_not] at hc
        exact hc
      have hIw : w ∈ I → l ∈ I → False := fun h1 h2 =>
        hind (Finset.mem_coe.mpr h2) (Finset.mem_coe.mpr h1) hlw.ne hlw
      rcases hwl a ha.1 ha.2 with rfl | rfl <;> rcases hwl b hb.1 hb.2 with rfl | rfl
      · rfl
      · exact (hIw ha.1 hb.1).elim
      · exact (hIw hb.1 ha.1).elim
      · rfl
    have h4 := Finset.card_filter_add_card_filter_not (s := I) p
    have h1 : G.indepNum = I.card := hI.2.symm
    omega
  · obtain ⟨t, ht⟩ := (G.induce {a | a ≠ w ∧ a ≠ l}).exists_isNIndepSet_indepNum
    have hlt : l ∉ t.map (Function.Embedding.subtype _) := by
      intro h
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
      exact a.2.2 ha
    have hJ : G.IsIndepSet ((insert l (t.map (Function.Embedding.subtype _)) : Finset V) : Set V) := by
      intro a ha b hb hab hadj
      simp only [Finset.coe_insert, Finset.coe_map, Set.mem_insert_iff, Set.mem_image,
        Finset.mem_coe, Function.Embedding.coe_subtype] at ha hb
      rcases ha with rfl | ⟨a', ha', rfl⟩ <;> rcases hb with rfl | ⟨b', hb', rfl⟩
      · exact hab rfl
      · exact b'.2.1 (hl _ hadj)
      · exact a'.2.1 (hl _ hadj.symm)
      · exact ht.1 ha' hb' (fun h => hab (by rw [h])) hadj
    have := hJ.card_le_indepNum
    rw [Finset.card_insert_of_notMem hlt, Finset.card_map, ht.2] at this
    exact this

/-- If `w` lies in every maximum independent set, deleting it lowers the independence number. -/
lemma indepNum_induce_lt_of_core (G : SimpleGraph V) (w : V)
    (hcore : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card = G.indepNum → w ∈ I) :
    (G.induce {a | a ≠ w}).indepNum + 1 ≤ G.indepNum := by
  obtain ⟨t, ht⟩ := (G.induce {a | a ≠ w}).exists_isNIndepSet_indepNum
  have hT : G.IsIndepSet ((t.map (Function.Embedding.subtype _) : Finset V) : Set V) := by
    intro a ha b hb hab hadj
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Function.Embedding.coe_subtype]
      at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ht.1 ha' hb' (fun h => hab (by rw [h])) hadj
  have hcard : (t.map (Function.Embedding.subtype _)).card =
      (G.induce {a | a ≠ w}).indepNum := by rw [Finset.card_map, ht.2]
  have hle := indepNum_induce_le G {a | a ≠ w}
  by_contra hlt
  have hmem := hcore _ hT (by omega)
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hmem
  exact a.2 ha

/-- Step 1 of D4: if `residue = indepNum`, a vertex of maximum degree lies outside some maximum
independent set. -/
lemma exists_max_indep_avoid (h3 : H3) (h4 : H4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V) (hedge : ∃ a b, G.Adj a b) (hmax : ∀ v, G.degree v ≤ G.degree w)
    (hR : G.residue = G.indepNum) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ I.card = G.indepNum ∧ w ∉ I := by
  by_contra hno
  have hcore : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card = G.indepNum → w ∈ I := by
    intro I hI hc
    by_contra hw
    exact hno ⟨I, hI, hc, hw⟩
  have h1 := indepNum_induce_lt_of_core G w hcore
  have h2 := h4 V G w hedge hmax
  have h3' := h3 {a : V // a ≠ w} (G.induce {a | a ≠ w})
  omega

/-- Splitting the independence number along `w`, a big part `C` and pendant vertices `L`. -/
lemma indepNum_split (G : SimpleGraph V) (w : V) (C L : Finset V) (hwC : w ∉ C) (hwL : w ∉ L)
    (hdisj : Disjoint C L) (hcov : ∀ a, a ≠ w → a ∈ C ∨ a ∈ L)
    (hLpend : ∀ l ∈ L, ∀ b, G.Adj l b → b = w)
    (havoid : ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ I.card = G.indepNum ∧ w ∉ I) :
    G.indepNum = (G.induce (C : Set V)).indepNum + L.card := by
  apply le_antisymm
  · obtain ⟨I, hIind, hIcard, hwI⟩ := havoid
    have hsplit : I ⊆ I.filter (fun a => a ∈ (C : Set V)) ∪ L := by
      intro a ha
      have haw : a ≠ w := fun h => hwI (h ▸ ha)
      rcases hcov a haw with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, Finset.mem_coe.mpr h⟩)
      · exact Finset.mem_union_right _ h
    have h1 := Finset.card_le_card hsplit
    have h2 := Finset.card_union_le (I.filter (fun a => a ∈ (C : Set V))) L
    have hsub : (G.induce (C : Set V)).IsIndepSet
        ((I.subtype (fun a => a ∈ (C : Set V)) : Finset _) : Set _) := by
      intro a ha b hb hab hadj
      rw [Finset.mem_coe, Finset.mem_subtype] at ha hb
      exact hIind (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
        (fun h => hab (Subtype.ext h)) hadj
    have h3 := hsub.card_le_indepNum
    rw [Finset.card_subtype] at h3
    omega
  · obtain ⟨t, ht⟩ := (G.induce (C : Set V)).exists_isNIndepSet_indepNum
    have hJ : G.IsIndepSet (((t.map (Function.Embedding.subtype _)) ∪ L : Finset V) : Set V) := by
      intro a ha b hb hab hadj
      simp only [Finset.coe_union, Finset.coe_map, Set.mem_union, Set.mem_image, Finset.mem_coe,
        Function.Embedding.coe_subtype] at ha hb
      rcases ha with ⟨a', ha', rfl⟩ | ha <;> rcases hb with ⟨b', hb', rfl⟩ | hb
      · exact ht.1 ha' hb' (fun h => hab (by rw [h])) hadj
      · exact hwC ((hLpend _ hb a' hadj.symm) ▸ Finset.mem_coe.mp a'.2)
      · exact hwC ((hLpend _ ha b' hadj) ▸ Finset.mem_coe.mp b'.2)
      · exact hwL ((hLpend _ ha _ hadj) ▸ hb)
    have hd : Disjoint (t.map (Function.Embedding.subtype _)) L := by
      rw [Finset.disjoint_left]
      intro a ha hL
      obtain ⟨a', _, rfl⟩ := Finset.mem_map.mp ha
      exact Finset.disjoint_left.mp hdisj (Finset.mem_coe.mp a'.2) hL
    have := hJ.card_le_indepNum
    rw [Finset.card_union_of_disjoint hd, Finset.card_map, ht.2] at this
    exact this

end indep_lemmas

section forest_lemmas

open Classical

variable {V : Type} [Fintype V]

/-- A connected nontrivial graph has an edge. -/
lemma exists_adj_of_connected [Nontrivial V] (G : SimpleGraph V) (hc : G.Connected) :
    ∃ a b, G.Adj a b := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  obtain ⟨p⟩ := hc.preconnected a b
  cases p with
  | nil => exact absurd rfl hab
  | cons h _ => exact ⟨_, _, h⟩

/-- The largest induced forest size is attained. -/
lemma exists_forest_eq (G : SimpleGraph V) :
    ∃ s : Finset V, (G.induce (s : Set V)).IsAcyclic ∧ s.card = G.largestInducedForestSize := by
  unfold largestInducedForestSize
  have hne : { n | ∃ s : Finset V, (G.induce (s : Set V)).IsAcyclic ∧ s.card = n }.Nonempty :=
    ⟨0, ∅, fun v => absurd v.2 (by simp), rfl⟩
  have hbdd : BddAbove { n | ∃ s : Finset V, (G.induce (s : Set V)).IsAcyclic ∧ s.card = n } :=
    ⟨Fintype.card V, by
      rintro n ⟨t, -, rfl⟩
      exact Finset.card_le_univ t⟩
  exact Nat.sSup_mem hne hbdd

/-- A forest of an induced subgraph, read in the whole graph. -/
lemma forest_induce_map_acyclic (G : SimpleGraph V) (s : Set V) (t : Finset s)
    (ht : ((G.induce s).induce (t : Set s)).IsAcyclic) :
    (G.induce ((t.map (Function.Embedding.subtype _) : Finset V) : Set V)).IsAcyclic := by
  have hs : ∀ x : ((t.map (Function.Embedding.subtype _) : Finset V) : Set V), (x : V) ∈ s := by
    intro x
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp (Finset.mem_coe.mp x.2)
    rw [← ha]
    exact a.2
  have htm : ∀ x : ((t.map (Function.Embedding.subtype _) : Finset V) : Set V),
      (⟨x.1, hs x⟩ : s) ∈ t := by
    intro x
    obtain ⟨a, ha, h⟩ := Finset.mem_map.mp (Finset.mem_coe.mp x.2)
    have : a = ⟨x.1, hs x⟩ := Subtype.ext h
    rw [← this]
    exact ha
  let f : G.induce ((t.map (Function.Embedding.subtype _) : Finset V) : Set V) ↪g
      (G.induce s).induce (t : Set s) :=
    { toFun := fun x => ⟨⟨x.1, hs x⟩, htm x⟩
      inj' := by
        intro x y hxy
        exact Subtype.ext (congrArg (fun z => z.1.1) hxy)
      map_rel_iff' := by
        intro x y
        exact Iff.rfl }
  exact IsAcyclic.embedding f ht

/-- Every induced subgraph has a smaller largest induced forest. -/
lemma forest_induce_le (G : SimpleGraph V) (s : Set V) :
    (G.induce s).largestInducedForestSize ≤ G.largestInducedForestSize := by
  unfold largestInducedForestSize
  apply csSup_le'
  rintro n ⟨t, ht, rfl⟩
  have hs : ∀ x : ((t.map (Function.Embedding.subtype _) : Finset V) : Set V), (x : V) ∈ s := by
    intro x
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp (Finset.mem_coe.mp x.2)
    rw [← ha]
    exact a.2
  have htm : ∀ x : ((t.map (Function.Embedding.subtype _) : Finset V) : Set V),
      (⟨x.1, hs x⟩ : s) ∈ t := by
    intro x
    obtain ⟨a, ha, h⟩ := Finset.mem_map.mp (Finset.mem_coe.mp x.2)
    have : a = ⟨x.1, hs x⟩ := Subtype.ext h
    rw [← this]
    exact ha
  let f : G.induce ((t.map (Function.Embedding.subtype _) : Finset V) : Set V) ↪g
      (G.induce s).induce (t : Set s) :=
    { toFun := fun x => ⟨⟨x.1, hs x⟩, htm x⟩
      inj' := by
        intro x y hxy
        exact Subtype.ext (congrArg (fun z => z.1.1) hxy)
      map_rel_iff' := by
        intro x y
        exact Iff.rfl }
  have hacyc : (G.induce ((t.map (Function.Embedding.subtype _) : Finset V) : Set V)).IsAcyclic :=
    IsAcyclic.embedding f ht
  have := card_le_forest G _ hacyc
  rw [Finset.card_map] at this
  exact this

/-- Step 0 of D4: in a connected nontrivial graph, `indepNum + 1 ≤ f`. -/
lemma indepNum_succ_le_forest [Nontrivial V] (G : SimpleGraph V) (hc : G.Connected) :
    G.indepNum + 1 ≤ G.largestInducedForestSize := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hind : G.IsIndepSet (I : Set V) := hI.1
  have hex : ∃ v, v ∉ I := by
    by_contra hall
    replace hall : ∀ v, v ∈ I := fun v => not_not.mp (not_exists.mp hall v)
    obtain ⟨a, b, hab⟩ := exists_adj_of_connected G hc
    exact hind (Finset.mem_coe.mpr (hall a)) (Finset.mem_coe.mpr (hall b)) hab.ne hab
  obtain ⟨v, hv⟩ := hex
  have hacyc := isAcyclic_induce_union G hc I {v} hind
    (by
      intro a ha b hb hab
      simp only [Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab)
  have := card_le_forest G (I ∪ {v}) hacyc
  rw [Finset.card_union_of_disjoint (by simpa using hv), hI.2, Finset.card_singleton] at this
  exact this

/-- An independent set `I` plus an independent set `J` such that each vertex of `I` has at most
one neighbour in `J` induces a forest. -/
lemma isAcyclic_induce_insert (G : SimpleGraph V) (I J : Finset V)
    (hI : G.IsIndepSet (I : Set V)) (hJ : G.IsIndepSet (J : Set V))
    (hleaf : ∀ x ∈ I, ∀ y ∈ J, ∀ y' ∈ J, G.Adj x y → G.Adj x y' → y = y') :
    (G.induce ((I ∪ J : Finset V) : Set V)).IsAcyclic := by
  apply isAcyclic_of_leaf_edges
  have leaf : ∀ x y : ((I ∪ J : Finset V) : Set V),
      (G.induce ((I ∪ J : Finset V) : Set V)).Adj x y → (x : V) ∈ I →
      ∀ z, (G.induce ((I ∪ J : Finset V) : Set V)).Adj x z → z = y := by
    intro x y hxy hx z hxz
    have hxy' : G.Adj x y := hxy
    have hxz' : G.Adj x z := hxz
    have memJ : ∀ w : ((I ∪ J : Finset V) : Set V), G.Adj x w → (w : V) ∈ J := by
      intro w hw
      have hw' := w.2
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hw'
      rcases hw' with hw' | hw'
      · exact absurd hw (hI (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hw') hw.ne)
      · exact hw'
    exact Subtype.ext (hleaf x hx z (memJ z hxz') y (memJ y hxy') hxz' hxy')
  intro x y hxy
  have hxy' : G.Adj x y := hxy
  by_cases hx : (x : V) ∈ I
  · exact Or.inl (leaf x y hxy hx)
  · right
    have hxJ : (x : V) ∈ J := by
      have hx' := x.2
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx'
      exact hx'.resolve_left hx
    have hy : (y : V) ∈ I := by
      have hy' := y.2
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hy'
      rcases hy' with hy' | hy'
      · exact hy'
      · exact absurd hxy' (hJ (Finset.mem_coe.mpr hxJ) (Finset.mem_coe.mpr hy') hxy'.ne)
    exact leaf y x hxy.symm hy

/-- A forest of `G.induce s` together with vertices all of whose neighbours lie outside `s ∪ L`
is again a forest. -/
lemma isAcyclic_induce_union_isolated (G : SimpleGraph V) (s : Finset V) (L : Finset V)
    (hs : (G.induce (s : Set V)).IsAcyclic) (hL : ∀ l ∈ L, ∀ b ∈ s ∪ L, ¬ G.Adj l b) :
    (G.induce ((s ∪ L : Finset V) : Set V)).IsAcyclic := by
  intro v c hc
  have hinj : Function.Injective (Embedding.induce (G := G) ((s ∪ L : Finset V) : Set V)).toHom :=
    Subtype.val_injective
  have hc' := hc.map hinj
  generalize hc'def : c.map (Embedding.induce (G := G) ((s ∪ L : Finset V) : Set V)).toHom = c' at hc'
  have hsup : ∀ x ∈ c'.support, x ∈ s ∪ L := by
    intro x hx
    rw [← hc'def, Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact Finset.mem_coe.mp y.2
  have hlen := hc'.three_le_length
  have hnoL : ∀ x ∈ c'.support, x ∉ L := by
    intro x hx hxL
    obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    rcases Nat.lt_or_ge i c'.length with hlt | hge
    · have hadj := c'.adj_getVert_succ hlt
      rw [hi] at hadj
      exact hL x hxL _ (hsup _ (Walk.getVert_mem_support c' (i + 1))) hadj
    · have hadj := c'.adj_getVert_succ (i := c'.length - 1) (by omega)
      have e : c'.length - 1 + 1 = i := by omega
      rw [e, hi] at hadj
      exact hL x hxL _ (hsup _ (Walk.getVert_mem_support c' (c'.length - 1))) hadj.symm
  have hall : ∀ x ∈ c'.support, x ∈ (s : Set V) := by
    intro x hx
    rcases Finset.mem_union.mp (hsup x hx) with h | h
    · exact Finset.mem_coe.mpr h
    · exact absurd h (hnoL x hx)
  have hmap := Walk.map_induce c' hall
  have hcyc : ((c'.induce (s : Set V) hall).map (Embedding.induce (G := G) (s : Set V)).toHom).IsCycle := by
    rw [hmap]
    exact hc'
  exact hs _ hcyc.of_map

/-- Step 3 of D4 (forest of two stars): if `U` is closed under neighbours other than `w`,
and edges `xx'`, `yy'` of `G - w` lie one inside and one outside `U`, then `f ≥ indepNum + 2`. -/
lemma forest_of_separated (G : SimpleGraph V) (w : V) (I : Finset V)
    (hI : G.IsIndepSet (I : Set V)) (hcard : I.card = G.indepNum) (hw : w ∉ I)
    (U : Finset V) (hwU : w ∉ U) (hclosed : ∀ a ∈ U, ∀ b, G.Adj a b → b ≠ w → b ∈ U)
    (x x' y y' : V) (hxx' : G.Adj x x') (hyy' : G.Adj y y') (hx : x ∈ U) (hx' : x' ∈ U)
    (hy : y ∉ U) (hy' : y' ∉ U) (hyw : y ≠ w) (hy'w : y' ≠ w) :
    G.indepNum + 2 ≤ G.largestInducedForestSize := by
  have pick : ∀ a a' : V, G.Adj a a' → ∃ t, (t = a ∨ t = a') ∧ t ∉ I := by
    intro a a' h
    by_cases ha : a ∈ I
    · exact ⟨a', Or.inr rfl, fun ha' => hI (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr ha') h.ne h⟩
    · exact ⟨a, Or.inl rfl, ha⟩
  obtain ⟨p, hp, hpI⟩ := pick x x' hxx'
  obtain ⟨q, hq, hqI⟩ := pick y y' hyy'
  have hpU : p ∈ U := by
    rcases hp with h | h
    · rw [h]; exact hx
    · rw [h]; exact hx'
  have hqU : q ∉ U := by
    rcases hq with h | h
    · rw [h]; exact hy
    · rw [h]; exact hy'
  have hqw : q ≠ w := by
    rcases hq with h | h
    · rw [h]; exact hyw
    · rw [h]; exact hy'w
  have hpq : p ≠ q := fun h => hqU (h ▸ hpU)
  have hnadj : ¬ G.Adj p q := fun h => hqU (hclosed p hpU q h hqw)
  have hJ : G.IsIndepSet (({p, q} : Finset V) : Set V) := by
    intro a ha c hc' hac hadj
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hc'
    rcases ha with ha | ha <;> rcases hc' with hc' | hc'
    · exact hac (ha.trans hc'.symm)
    · rw [ha, hc'] at hadj
      exact hnadj hadj
    · rw [ha, hc'] at hadj
      exact hnadj hadj.symm
    · exact hac (ha.trans hc'.symm)
  have hleaf : ∀ a ∈ I, ∀ r ∈ ({p, q} : Finset V), ∀ r' ∈ ({p, q} : Finset V),
      G.Adj a r → G.Adj a r' → r = r' := by
    intro a ha r hr r' hr' h1 h2
    have haw : a ≠ w := fun h => hw (h ▸ ha)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr hr'
    rcases hr with hr | hr <;> rcases hr' with hr' | hr'
    · rw [hr, hr']
    · rw [hr] at h1
      rw [hr'] at h2
      exact absurd (hclosed a (hclosed p hpU a h1.symm haw) q h2 hqw) hqU
    · rw [hr'] at h2
      rw [hr] at h1
      exact absurd (hclosed a (hclosed p hpU a h2.symm haw) q h1 hqw) hqU
    · rw [hr, hr']
  have hacyc := isAcyclic_induce_insert G I {p, q} hI hJ hleaf
  have hcd := card_le_forest G (I ∪ {p, q}) hacyc
  have hdisj : Disjoint I {p, q} := by
    rw [Finset.disjoint_right]
    intro a ha hai
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hpI hai
    · exact hqI hai
  rw [Finset.card_union_of_disjoint hdisj, hcard, Finset.card_pair hpq] at hcd
  exact hcd

/-- L5. If `f ≤ indepNum + 1`, every pair at distance at least three meets every maximum
independent set. -/
lemma core_of_far [Nontrivial V] (G : SimpleGraph V) (hc : G.Connected)
    (hF : G.largestInducedForestSize ≤ G.indepNum + 1) (I : Finset V)
    (hI : G.IsIndepSet (I : Set V)) (hcard : I.card = G.indepNum) (x y : V)
    (hxy : 3 ≤ G.dist x y) : x ∈ I ∨ y ∈ I := by
  by_contra hne
  have hxI : x ∉ I := fun h => hne (Or.inl h)
  have hyI : y ∉ I := fun h => hne (Or.inr h)
  have hxy' : x ≠ y := by
    intro h
    rw [h, SimpleGraph.dist_self] at hxy
    omega
  have hacyc := isAcyclic_induce_union G hc I {x, y} hI
    (by
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hxy
      · rw [SimpleGraph.dist_comm]; exact hxy
      · exact absurd rfl hab)
  have := card_le_forest G (I ∪ {x, y}) hacyc
  rw [Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact hxI ha
      · exact hyI ha), hcard, Finset.card_pair hxy'] at this
  omega

/-- L5, consequence. If `f ≤ indepNum + 1`, the ends of a pair at distance four lie in every
maximum independent set. -/
lemma core_endpoints [Nontrivial V] (G : SimpleGraph V) (hc : G.Connected)
    (hF : G.largestInducedForestSize ≤ G.indepNum + 1) (I : Finset V)
    (hI : G.IsIndepSet (I : Set V)) (hcard : I.card = G.indepNum) (x y : V)
    (hxy : G.dist x y = 4) : x ∈ I ∧ y ∈ I := by
  have key : ∀ x y : V, G.dist x y = 4 → x ∈ I := by
    intro x y hxy
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
    have hlen : p.length = 4 := hp.trans hxy
    have hdz : G.dist x (p.getVert 3) = 3 := dist_getVert_of_shortest hc p hp 3 (by omega)
    have hadj : G.Adj (p.getVert 3) y := by
      have h := p.adj_getVert_succ (i := 3) (by omega)
      have h4 : p.getVert 4 = y := by
        have := p.getVert_length
        rwa [hlen] at this
      rwa [h4] at h
    by_contra hx
    have h1 := core_of_far G hc hF I hI hcard x (p.getVert 3) (by omega)
    have h2 := core_of_far G hc hF I hI hcard x y (by omega)
    have hz' := h1.resolve_left hx
    have hy' := h2.resolve_left hx
    exact hI (Finset.mem_coe.mpr hz') (Finset.mem_coe.mpr hy') hadj.ne hadj
  exact ⟨key x y hxy, key y x (by rw [SimpleGraph.dist_comm]; exact hxy)⟩

end forest_lemmas

section dist_lemmas

open Classical

variable {V : Type} [Fintype V]

/-- Distances do not decrease when passing to a connected induced subgraph. -/
lemma dist_le_dist_induce (G : SimpleGraph V) (s : Set V) (x y : s)
    (h : (G.induce s).Reachable x y) : G.dist x y ≤ (G.induce s).dist x y := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  have := dist_le (p.map (Embedding.induce s).toHom)
  rw [Walk.length_map] at this
  rw [← hp]
  exact this

/-- A geodesic of `G` between two vertices of a connected induced subgraph bounds its
diameter. -/
lemma le_diam_induce (G : SimpleGraph V) (s : Set V) (hs : (G.induce s).Connected)
    (x y : V) (hx : x ∈ s) (hy : y ∈ s) : G.dist x y ≤ (G.induce s).diam := by
  have h1 := dist_le_dist_induce G s ⟨x, hx⟩ ⟨y, hy⟩ (hs.preconnected _ _)
  haveI : Nonempty s := ⟨⟨x, hx⟩⟩
  have h2 : (G.induce s).ediam ≠ ⊤ := (connected_iff_ediam_ne_top).mp hs
  exact h1.trans (dist_le_diam h2)

end dist_lemmas

section twoswitch_aux

open Finset
open scoped Classical

lemma twoSwitchAux_neighborFinset_v {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) {v x y z : V} (hT : ∀ a c, T.Adj a c ↔ (if s(a, c) = s(v, x) then False else if s(a, c) = s(y, z) then False else if s(a, c) = s(v, y) then True else if s(a, c) = s(x, z) then True else G.Adj a c))
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    T.neighborFinset v = insert y ((G.neighborFinset v).erase x) := by
  ext a
  rw [mem_insert, mem_erase, mem_neighborFinset, mem_neighborFinset]
  simp only [hT]
  by_cases hay : a = y
  · rw [hay]
    have h1 : s(v, y) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h2 : s(v, y) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    simp [h1, h2, hxy.symm]
  · by_cases hax : a = x
    · rw [hax] at hay ⊢
      have h1 : s(v, x) = s(v, x) := rfl
      rw [if_pos h1]
      simp [hay]
    · have h1 : s(v, a) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(v, a) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h3 : s(v, a) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h4 : s(v, a) ≠ s(x, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      simp [hay, hax, h1, h2, h3, h4]

lemma twoSwitchAux_neighborFinset_x {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) {v x y z : V} (hT : ∀ a c, T.Adj a c ↔ (if s(a, c) = s(v, x) then False else if s(a, c) = s(y, z) then False else if s(a, c) = s(v, y) then True else if s(a, c) = s(x, z) then True else G.Adj a c))
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (_hxz : x ≠ z) (_hyz : y ≠ z) :
    T.neighborFinset x = insert z ((G.neighborFinset x).erase v) := by
  ext a
  rw [mem_insert, mem_erase, mem_neighborFinset, mem_neighborFinset]
  simp only [hT]
  by_cases haz : a = z
  · rw [haz]
    have h1 : s(x, z) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h2 : s(x, z) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h3 : s(x, z) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    simp [h1, h2, h3, hvz.symm]
  · by_cases hav : a = v
    · rw [hav] at haz ⊢
      have h1 : s(x, v) = s(v, x) := Sym2.eq_swap
      rw [if_pos h1]
      simp [haz]
    · have h1 : s(x, a) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(x, a) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h3 : s(x, a) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h4 : s(x, a) ≠ s(x, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      simp [haz, hav, h1, h2, h3, h4]

lemma twoSwitchAux_neighborFinset_y {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) {v x y z : V} (hT : ∀ a c, T.Adj a c ↔ (if s(a, c) = s(v, x) then False else if s(a, c) = s(y, z) then False else if s(a, c) = s(v, y) then True else if s(a, c) = s(x, z) then True else G.Adj a c))
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    T.neighborFinset y = insert v ((G.neighborFinset y).erase z) := by
  ext a
  rw [mem_insert, mem_erase, mem_neighborFinset, mem_neighborFinset]
  simp only [hT]
  by_cases hav : a = v
  · rw [hav]
    have h1 : s(y, v) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h2 : s(y, v) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h3 : s(y, v) = s(v, y) := Sym2.eq_swap
    rw [if_neg h1, if_neg h2, if_pos h3]
    simp
  · by_cases haz : a = z
    · rw [haz] at hav ⊢
      have h1 : s(y, z) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      rw [if_neg h1, if_pos rfl]
      simp [hav]
    · have h1 : s(y, a) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(y, a) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h3 : s(y, a) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h4 : s(y, a) ≠ s(x, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      simp [hav, haz, h1, h2, h3, h4]

lemma twoSwitchAux_neighborFinset_z {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) {v x y z : V} (hT : ∀ a c, T.Adj a c ↔ (if s(a, c) = s(v, x) then False else if s(a, c) = s(y, z) then False else if s(a, c) = s(v, y) then True else if s(a, c) = s(x, z) then True else G.Adj a c))
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    T.neighborFinset z = insert x ((G.neighborFinset z).erase y) := by
  ext a
  rw [mem_insert, mem_erase, mem_neighborFinset, mem_neighborFinset]
  simp only [hT]
  by_cases hax : a = x
  · rw [hax]
    have h1 : s(z, x) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h2 : s(z, x) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h3 : s(z, x) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h4 : s(z, x) = s(x, z) := Sym2.eq_swap
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    simp
  · by_cases hay : a = y
    · rw [hay] at hax ⊢
      have h1 : s(z, y) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(z, y) = s(y, z) := Sym2.eq_swap
      rw [if_neg h1, if_pos h2]
      simp [hax]
    · have h1 : s(z, a) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(z, a) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h3 : s(z, a) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h4 : s(z, a) ≠ s(x, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      simp [hax, hay, h1, h2, h3, h4]

lemma twoSwitchAux_neighborFinset_other {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) {v x y z a : V} (hT : ∀ a c, T.Adj a c ↔ (if s(a, c) = s(v, x) then False else if s(a, c) = s(y, z) then False else if s(a, c) = s(v, y) then True else if s(a, c) = s(x, z) then True else G.Adj a c))
    (hvy : v ≠ y) (hxz : x ≠ z) (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z) :
    T.neighborFinset a = G.neighborFinset a := by
  ext b
  rw [mem_neighborFinset, mem_neighborFinset]
  simp only [hT]
  have h1 : s(a, b) ≠ s(v, x) := by
    rw [ne_eq, Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact hav h; exact hax h]
  have h2 : s(a, b) ≠ s(y, z) := by
    rw [ne_eq, Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact hay h; exact haz h]
  have h3 : s(a, b) ≠ s(v, y) := by
    rw [ne_eq, Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact hav h; exact hay h]
  have h4 : s(a, b) ≠ s(x, z) := by
    rw [ne_eq, Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact hax h; exact haz h]
  simp [h1, h2, h3, h4]

lemma twoSwitchAux_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) {v x y z : V} (hT : ∀ a c, T.Adj a c ↔ (if s(a, c) = s(v, x) then False else if s(a, c) = s(y, z) then False else if s(a, c) = s(v, y) then True else if s(a, c) = s(x, z) then True else G.Adj a c))
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : G.Adj v x) (h2 : G.Adj y z) (h3 : ¬ G.Adj v y) (h4 : ¬ G.Adj x z) :
    ∀ a, T.degree a = G.degree a := by
  intro a
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  by_cases hav : a = v
  · subst hav; rw [twoSwitchAux_neighborFinset_v G T hT hvx hvy hvz hxy hxz hyz,
      card_insert_of_notMem (by simp [mem_neighborFinset, h3, hxy.symm]),
      card_erase_add_one (by rw [mem_neighborFinset]; exact h1)]
  · by_cases hax : a = x
    · subst hax; rw [twoSwitchAux_neighborFinset_x G T hT hvx hvy hvz hxy hxz hyz,
        card_insert_of_notMem (by simp [mem_neighborFinset, h4, hvz.symm]),
        card_erase_add_one (by rw [mem_neighborFinset]; exact (G.adj_comm _ _).1 h1)]
    · by_cases hay : a = y
      · subst hay; rw [twoSwitchAux_neighborFinset_y G T hT hvx hvy hvz hxy hxz hyz,
          card_insert_of_notMem (by simp [mem_neighborFinset, G.adj_comm, h3, hvz]),
          card_erase_add_one (by rw [mem_neighborFinset]; exact h2)]
      · by_cases haz : a = z
        · subst haz; rw [twoSwitchAux_neighborFinset_z G T hT hvx hvy hvz hxy hxz hyz,
            card_insert_of_notMem (by simp [mem_neighborFinset, G.adj_comm, h4, hxy]),
            card_erase_add_one (by rw [mem_neighborFinset]; exact (G.adj_comm _ _).1 h2)]
        · rw [twoSwitchAux_neighborFinset_other G T hT hvy hxz hav hax hay haz]

end twoswitch_aux

section switch_lemmas

open Classical

variable {V : Type} [Fintype V]

/-- The edge exchange `G - wl - zb + wb + lz`, given by its adjacency, with the same degrees. -/
lemma exists_two_switch (G : SimpleGraph V) [DecidableRel G.Adj] (w l z b : V)
    (hwl : G.Adj w l) (hzb : G.Adj z b) (hwb : ¬ G.Adj w b) (hlz : ¬ G.Adj l z)
    (hwz : w ≠ z) (hwb' : w ≠ b) (hlz' : l ≠ z) (hlb : l ≠ b) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, (∀ v, H.degree v = G.degree v) ∧
      H.Adj w b ∧
      (∀ x y, x ≠ w → y ≠ w →
        (H.Adj x y ↔ (G.Adj x y ∧ ¬ s(x, y) = s(z, b)) ∨ s(x, y) = s(l, z))) := by
  classical
  have hne1 : ¬ s(w, b) = s(w, l) := by
    rw [Sym2.eq_iff]; rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact hlb h.symm
    · exact hwl.ne h
  have hne2 : ¬ s(w, b) = s(b, z) := by
    rw [Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hwb' h
    · exact hwz h
  have hbl : ¬ s(b, z) = s(l, z) := by
    rw [Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hlb h.symm
    · exact hzb.ne h.symm
  let T : SimpleGraph V :=
    { Adj := fun a c =>
        if s(a, c) = s(w, l) then False
        else if s(a, c) = s(b, z) then False
        else if s(a, c) = s(w, b) then True
        else if s(a, c) = s(l, z) then True
        else G.Adj a c
      symm := ⟨fun a c h => by
        rw [Sym2.eq_swap]
        split_ifs at h ⊢ <;> (first | exact h | exact (G.adj_comm _ _).1 h)⟩
      loopless := ⟨fun a h => by
        by_cases h1 : s(a, a) = s(w, l)
        · simp only [h1, ↓reduceIte] at h
        · by_cases h2 : s(a, a) = s(b, z)
          · split_ifs at h
          · by_cases h3 : s(a, a) = s(w, b)
            · rw [Sym2.eq_iff] at h3
              rcases h3 with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
              · exact hwb' (ha1.symm.trans ha2)
              · exact hwb' (ha2.symm.trans ha1)
            · by_cases h4 : s(a, a) = s(l, z)
              · rw [Sym2.eq_iff] at h4
                rcases h4 with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
                · exact hlz' (ha1.symm.trans ha2)
                · exact hlz' (ha2.symm.trans ha1)
              · simp only [h1, h2, h3, h4, ↓reduceIte] at h
                exact G.loopless.irrefl a h⟩ }
  have hT : ∀ a c, T.Adj a c ↔ (if s(a, c) = s(w, l) then False else if s(a, c) = s(b, z) then False
      else if s(a, c) = s(w, b) then True else if s(a, c) = s(l, z) then True else G.Adj a c) :=
    fun a c => Iff.rfl
  refine ⟨T, fun a c => Classical.propDecidable _, ?_, ?_, ?_⟩
  · intro a
    convert twoSwitchAux_degree_eq G T hT hwl.ne hwb' hwz hlb hlz' hzb.ne.symm hwl hzb.symm hwb
      hlz a
  · show (if s(w, b) = s(w, l) then False else if s(w, b) = s(b, z) then False
      else if s(w, b) = s(w, b) then True else if s(w, b) = s(l, z) then True else G.Adj w b)
    rw [if_neg hne1, if_neg hne2, if_pos rfl]
    trivial
  · intro p q hp hq
    show (if s(p, q) = s(w, l) then False else if s(p, q) = s(b, z) then False
      else if s(p, q) = s(w, b) then True else if s(p, q) = s(l, z) then True else G.Adj p q) ↔ _
    have e1 : ¬ s(p, q) = s(w, l) := by
      rw [Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact hp h
      · exact hq h
    have e3 : ¬ s(p, q) = s(w, b) := by
      rw [Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact hp h
      · exact hq h
    rw [if_neg e1]
    by_cases e2 : s(p, q) = s(b, z)
    · rw [if_pos e2]
      have e5 : s(p, q) = s(z, b) := e2.trans Sym2.eq_swap
      have e4 : ¬ s(p, q) = s(l, z) := fun h => hbl (e2.symm.trans h)
      constructor
      · exact False.elim
      · rintro (⟨_, h⟩ | h)
        · exact h e5
        · exact e4 h
    · rw [if_neg e2, if_neg e3]
      have e2' : ¬ s(p, q) = s(z, b) := fun h => e2 (h.trans Sym2.eq_swap)
      by_cases e4 : s(p, q) = s(l, z)
      · rw [if_pos e4]; simp [e4]
      · rw [if_neg e4]; simp [e2', e4]

/-- After the exchange, `H - w` has independence number at most that of `G - {w, l}`, because
`z` lies in every maximum independent set of `G - {w, l}`. -/
lemma indepNum_switch_le (G H : SimpleGraph V) (w l z b : V) (hlw : G.Adj l w)
    (hl : ∀ c, G.Adj l c → c = w) (hzw : z ≠ w) (hzl : z ≠ l) (hzb : G.Adj z b) (hbw : b ≠ w)
    (hH : ∀ x y, x ≠ w → y ≠ w →
        (H.Adj x y ↔ (G.Adj x y ∧ ¬ s(x, y) = s(z, b)) ∨ s(x, y) = s(l, z)))
    (hz : ∀ t : Finset V, G.IsIndepSet (t : Set V) → (∀ a ∈ t, a ≠ w ∧ a ≠ l) →
      t.card = (G.induce {a | a ≠ w ∧ a ≠ l}).indepNum → z ∈ t) :
    (H.induce {a | a ≠ w}).indepNum ≤ (G.induce {a | a ≠ w ∧ a ≠ l}).indepNum := by
  classical
  obtain ⟨t, ht⟩ := (H.induce {a | a ≠ w}).exists_isNIndepSet_indepNum
  have hTw : ∀ a ∈ t.map (Function.Embedding.subtype _), a ≠ w := by
    intro a ha
    obtain ⟨a', _, rfl⟩ := Finset.mem_map.mp ha
    exact a'.2
  have hTind : ∀ x ∈ t.map (Function.Embedding.subtype _),
      ∀ y ∈ t.map (Function.Embedding.subtype _), ¬ H.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    exact ht.1 (Finset.mem_coe.mpr hx') (Finset.mem_coe.mpr hy')
      (fun h => hxy.ne (congrArg Subtype.val h)) hxy
  have hGind : ∀ U : Finset V, U ⊆ t.map (Function.Embedding.subtype _) →
      ¬ (z ∈ U ∧ b ∈ U) → G.IsIndepSet (U : Set V) := by
    intro U hU hzb' x hx y hy hxy hadj
    have hxT := hU (Finset.mem_coe.mp hx)
    have hyT := hU (Finset.mem_coe.mp hy)
    by_cases he : s(x, y) = s(z, b)
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hzb' ⟨h1 ▸ Finset.mem_coe.mp hx, h2 ▸ Finset.mem_coe.mp hy⟩
      · exact hzb' ⟨h2 ▸ Finset.mem_coe.mp hy, h1 ▸ Finset.mem_coe.mp hx⟩
    · exact hTind x hxT y hyT ((hH x y (hTw x hxT) (hTw y hyT)).mpr (Or.inl ⟨hadj, he⟩))
  have hU' : ∀ U : Finset V, G.IsIndepSet (U : Set V) → (∀ a ∈ U, a ≠ w ∧ a ≠ l) →
      U.card ≤ (G.induce {a | a ≠ w ∧ a ≠ l}).indepNum := by
    intro U hU hav
    let p : V → Prop := fun a => a ∈ {a : V | a ≠ w ∧ a ≠ l}
    have hsub : (G.induce {a | a ≠ w ∧ a ≠ l}).IsIndepSet ((U.subtype p : Finset _) : Set _) := by
      intro a ha b hb hab hadj
      rw [Finset.mem_coe, Finset.mem_subtype] at ha hb
      exact hU (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
        (fun h => hab (Subtype.ext h)) hadj
    have h2 := hsub.card_le_indepNum
    have hf : U.filter p = U := Finset.filter_true_of_mem (fun a ha => hav a ha)
    rw [Finset.card_subtype, hf] at h2
    exact h2
  have hU : ∀ U : Finset V, G.IsIndepSet (U : Set V) → (∀ a ∈ U, a ≠ w ∧ a ≠ l) → z ∉ U →
      U.card + 1 ≤ (G.induce {a | a ≠ w ∧ a ≠ l}).indepNum := by
    intro U hI hav hzU
    have h1 := hU' U hI hav
    by_contra hlt
    exact hzU (hz U hI hav (by omega))
  have hcard : (t.map (Function.Embedding.subtype _)).card =
      (H.induce {a | a ≠ w}).indepNum := by rw [Finset.card_map, ht.2]
  rw [← hcard]
  set T := t.map (Function.Embedding.subtype _) with hTdef
  by_cases hlT : l ∈ T
  · have hzT : z ∉ T := fun hzT =>
      hTind l hlT z hzT ((hH l z hlw.ne hzw).mpr (Or.inr rfl))
    have hzE : z ∉ T.erase l := fun h => hzT (Finset.mem_of_mem_erase h)
    have h1 := hU (T.erase l) (hGind _ (Finset.erase_subset _ _) (fun h => hzE h.1))
      (fun a ha => ⟨hTw a (Finset.mem_of_mem_erase ha), Finset.ne_of_mem_erase ha⟩) hzE
    have h2 := Finset.card_erase_add_one hlT
    omega
  · by_cases hzb' : z ∈ T ∧ b ∈ T
    · have hzE : z ∉ T.erase z := by simp
      have h1 := hU (T.erase z) (hGind _ (Finset.erase_subset _ _) (fun h => hzE h.1))
        (fun a ha => ⟨hTw a (Finset.mem_of_mem_erase ha), fun h => hlT (h ▸ Finset.mem_of_mem_erase ha)⟩)
        hzE
      have h2 := Finset.card_erase_add_one hzb'.1
      omega
    · have h1 := hU' T (hGind T (subset_refl _) hzb')
        (fun a ha => ⟨hTw a ha, fun h => hlT (h ▸ ha)⟩)
      exact h1

/-- L7. Pendant exchange. -/
lemma residue_pendant_switch (h3 : H3) (h4 : H4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (w l z b : V) (hmax : ∀ v, G.degree v ≤ G.degree w) (hlw : G.Adj l w)
    (hl : ∀ c, G.Adj l c → c = w) (hzw : z ≠ w) (hzl : z ≠ l) (hzb : G.Adj z b)
    (hwb : ¬ G.Adj w b) (hbw : b ≠ w)
    (hz : ∀ t : Finset V, G.IsIndepSet (t : Set V) → (∀ a ∈ t, a ≠ w ∧ a ≠ l) →
      t.card = (G.induce {a | a ≠ w ∧ a ≠ l}).indepNum → z ∈ t) :
    G.residue + 1 ≤ G.indepNum := by
  have hlz : ¬ G.Adj l z := fun h => hzw (hl z h)
  have hlb : l ≠ b := fun h => hlz (h ▸ hzb.symm)
  obtain ⟨H, hdec, hdeg, hHwb, hH⟩ :=
    exists_two_switch G w l z b hlw.symm hzb hwb hlz hzw.symm hbw.symm hzl.symm hlb
  have hres : G.residue = H.residue := residue_congr_degree G H (fun v => (hdeg v).symm)
  have hmaxH : ∀ v, H.degree v ≤ H.degree w := fun v => by
    rw [hdeg v, hdeg w]
    exact hmax v
  have h4' := h4 V H w ⟨w, b, hHwb⟩ hmaxH
  have h3' := h3 {a : V // a ≠ w} (H.induce {a | a ≠ w})
  have hsw := indepNum_switch_le G H w l z b hlw hl hzw hzl hzb hbw hH hz
  have h6 := indepNum_pendant G w l hlw hl
  omega

end switch_lemmas

section d4_lemmas

open Classical

variable {V : Type} [Fintype V]

/-- Step 2 of D4: if `G - w` is connected and contains a pair at distance four, the induction
hypothesis (or the bound `indepNum + (diam + 3) / 4 ≤ f`) gives the result. -/
lemma step2 (h3 : H3) (h4 : H4) (n : ℕ)
    (IH : ∀ (W : Type) [Fintype W] [DecidableEq W] [Nontrivial W] (K : SimpleGraph W)
      [DecidableRel K.Adj], Fintype.card W < n → K.Connected → K.diam = 4 →
      K.residue + 2 ≤ K.largestInducedForestSize)
    (hn : Fintype.card V = n) (G : SimpleGraph V) [DecidableRel G.Adj] (w : V)
    (hedge : ∃ a b, G.Adj a b) (hmax : ∀ v, G.degree v ≤ G.degree w)
    (hconn : (G.induce {a | a ≠ w}).Connected) (x y : V) (hx : x ≠ w) (hy : y ≠ w)
    (hxy : G.dist x y = 4) :
    G.residue + 2 ≤ G.largestInducedForestSize := by
  have hy4 : G.dist x y ≤ (G.induce {a | a ≠ w}).diam :=
    le_diam_induce G {a | a ≠ w} hconn x y hx hy
  have hxy : x ≠ y := by
    intro h
    rw [h, SimpleGraph.dist_self] at hxy
    omega
  haveI : Nontrivial ↥({a | a ≠ w} : Set V) :=
    ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩⟩
  have hcardW : Fintype.card {a : V // a ≠ w} < n := by
    rw [← hn]
    exact Fintype.card_subtype_lt (p := fun a => a ≠ w) (x := w) (by simp)
  have hK : (G.induce {a | a ≠ w}).residue + 2 ≤ (G.induce {a | a ≠ w}).largestInducedForestSize := by
    by_cases hd4 : (G.induce {a | a ≠ w}).diam = 4
    · exact IH ↥({a | a ≠ w} : Set V) (G.induce {a | a ≠ w}) hcardW hconn hd4
    · have h5 := indepNum_add_le_forest (G.induce {a | a ≠ w}) hconn
      have h6 := h3 ↥({a | a ≠ w} : Set V) (G.induce {a | a ≠ w})
      omega
  have h7 := h4 V G w hedge hmax
  have h8 := forest_induce_le G {a | a ≠ w}
  omega

/-- Step 3 of D4, first part: two edges of `G - w` lie in the same component of `G - w`. -/
lemma step3_reach (G : SimpleGraph V) (w : V)
    (hF : G.largestInducedForestSize ≤ G.indepNum + 1)
    (havoid : ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ I.card = G.indepNum ∧ w ∉ I)
    (x x' y y' : V) (hxx' : G.Adj x x') (hyy' : G.Adj y y') (hx : x ≠ w) (hx' : x' ≠ w)
    (hy : y ≠ w) (hy' : y' ≠ w) :
    (G.induce {a | a ≠ w}).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  by_contra hnr
  obtain ⟨I, hI, hcard, hwI⟩ := havoid
  let U : Finset V := Finset.univ.filter
    (fun a => ∃ h : a ≠ w, (G.induce {a | a ≠ w}).Reachable ⟨x, hx⟩ ⟨a, h⟩)
  have hU : ∀ a, a ∈ U ↔ ∃ h : a ≠ w, (G.induce {a | a ≠ w}).Reachable ⟨x, hx⟩ ⟨a, h⟩ := by
    intro a
    simp [U]
  have hxU : x ∈ U := (hU x).mpr ⟨hx, Reachable.refl _⟩
  have hx'U : x' ∈ U := (hU x').mpr ⟨hx', (Adj.reachable (show (G.induce {a | a ≠ w}).Adj
    ⟨x, hx⟩ ⟨x', hx'⟩ from hxx'))⟩
  have hyU : y ∉ U := fun h => by
    obtain ⟨h1, h2⟩ := (hU y).mp h
    exact hnr h2
  have hy'U : y' ∉ U := fun h => by
    obtain ⟨h1, h2⟩ := (hU y').mp h
    exact hnr (h2.trans (Adj.reachable (show (G.induce {a | a ≠ w}).Adj ⟨y', hy'⟩ ⟨y, hy⟩
      from hyy'.symm)))
  have hwU : w ∉ U := fun h => by
    obtain ⟨h1, _⟩ := (hU w).mp h
    exact h1 rfl
  have hclosed : ∀ a ∈ U, ∀ b, G.Adj a b → b ≠ w → b ∈ U := by
    intro a ha b hab hb
    obtain ⟨h1, h2⟩ := (hU a).mp ha
    exact (hU b).mpr ⟨hb, h2.trans (Adj.reachable (show (G.induce {a | a ≠ w}).Adj
      ⟨a, h1⟩ ⟨b, hb⟩ from hab))⟩
  have := forest_of_separated G w I hI hcard hwI U hwU hclosed x x' y y' hxx' hyy' hxU hx'U
    hyU hy'U hy hy'
  omega

/-- A connected nontrivial graph of diameter four has an edge avoiding any given vertex. -/
lemma step3_active_exists [Nontrivial V] (G : SimpleGraph V) (hc : G.Connected)
    (hd : G.diam = 4) (w : V) : ∃ x x', G.Adj x x' ∧ x ≠ w ∧ x' ≠ w := by
  by_contra hno
  have hno' : ∀ x x', G.Adj x x' → x = w ∨ x' = w := by
    intro x x' h
    by_contra h'
    exact hno ⟨x, x', h, fun e => h' (Or.inl e), fun e => h' (Or.inr e)⟩
  have hnb : ∀ a, a ≠ w → G.Adj a w := by
    intro a ha
    obtain ⟨p⟩ := hc.preconnected a w
    cases p with
    | nil => exact absurd rfl ha
    | cons h _ =>
      rename_i b
      rcases hno' _ _ h with e | e
      · exact absurd e ha
      · rw [← e]; exact h
  obtain ⟨x, y, hxy⟩ := G.exists_dist_eq_diam
  rw [hd] at hxy
  have h2 : G.dist x y ≤ 2 := by
    by_cases hx : x = w
    · by_cases hy : y = w
      · rw [hx, hy, SimpleGraph.dist_self]; omega
      · have := SimpleGraph.dist_eq_one_iff_adj.mpr (hnb y hy).symm
        rw [hx]; omega
    · by_cases hy : y = w
      · have := SimpleGraph.dist_eq_one_iff_adj.mpr (hnb x hx)
        rw [hy]; omega
      · have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr (hnb x hx)
        have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr (hnb y hy).symm
        have := hc.dist_triangle (u := x) (v := w) (w := y)
        omega
  omega

/-- Step 3 of D4: the shape of `G - w` when it is disconnected. -/
lemma step3_structure (G : SimpleGraph V) [Nontrivial V] (hc : G.Connected) (hd : G.diam = 4)
    (w : V) (hF : G.largestInducedForestSize ≤ G.indepNum + 1)
    (havoid : ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ I.card = G.indepNum ∧ w ∉ I)
    (hdisc : ¬ (G.induce {a | a ≠ w}).Connected) :
    ∃ C L : Finset V, Disjoint C L ∧ w ∉ C ∧ w ∉ L ∧ (∀ a, a ≠ w → a ∈ C ∨ a ∈ L) ∧
      L.Nonempty ∧ (G.induce (C : Set V)).Connected ∧ 2 ≤ C.card ∧
      (∀ l ∈ L, G.Adj l w) ∧ (∀ l ∈ L, ∀ b, G.Adj l b → b = w) := by
  obtain ⟨x0, x0', h00, hx0, hx0'⟩ := step3_active_exists G hc hd w
  let P : V → Prop := fun a =>
    ∃ h : a ≠ w, (G.induce {a | a ≠ w}).Reachable ⟨a, h⟩ ⟨x0, hx0⟩
  let C : Finset V := Finset.univ.filter P
  let L : Finset V := Finset.univ.filter (fun a => a ≠ w ∧ ¬ P a)
  have hC : ∀ a, a ∈ C ↔ P a := by
    intro a
    simp [C]
  have hL : ∀ a, a ∈ L ↔ a ≠ w ∧ ¬ P a := by
    intro a
    simp [L]
  have hnbr : ∀ a, a ≠ w → ∃ b, G.Adj a b := by
    intro a ha
    obtain ⟨p⟩ := hc.preconnected a w
    cases p with
    | nil => exact absurd rfl ha
    | cons h _ => exact ⟨_, h⟩
  have hLpend : ∀ l ∈ L, ∀ b, G.Adj l b → b = w := by
    intro l hl b hlb
    obtain ⟨hlw, hPl⟩ := (hL l).mp hl
    by_contra hb
    exact hPl ⟨hlw, step3_reach G w hF havoid l b x0 x0' hlb h00 hlw hb hx0 hx0'⟩
  have hLw : ∀ l ∈ L, G.Adj l w := by
    intro l hl
    obtain ⟨b, hb⟩ := hnbr l ((hL l).mp hl).1
    rw [← hLpend l hl b hb]
    exact hb
  have hPclosed : ∀ (u v : ↥{a | a ≠ w}), (G.induce {a | a ≠ w}).Adj u v → P u.1 → P v.1 := by
    intro u v huv ⟨h, hr⟩
    exact ⟨v.2, (Adj.reachable huv.symm).trans hr⟩
  have hx0P : P x0 := ⟨hx0, Reachable.refl _⟩
  have hx0'P : P x0' := ⟨hx0', Adj.reachable (show (G.induce {a | a ≠ w}).Adj ⟨x0', hx0'⟩
    ⟨x0, hx0⟩ from h00.symm)⟩
  have hLne : L.Nonempty := by
    by_contra hemp
    apply hdisc
    have hall : ∀ a, a ≠ w → P a := by
      intro a ha
      by_contra hPa
      exact hemp ⟨a, (hL a).mpr ⟨ha, hPa⟩⟩
    refine ((G.induce _).connected_iff).mpr ⟨?_, ⟨⟨x0, hx0⟩⟩⟩
    intro u v
    obtain ⟨h1, r1⟩ := hall u.1 u.2
    obtain ⟨h2, r2⟩ := hall v.1 v.2
    exact r1.trans r2.symm
  let toC : ∀ a, P a → ↥(C : Set V) := fun a h => ⟨a, Finset.mem_coe.mpr ((hC a).mpr h)⟩
  have claim : ∀ (u v : ↥{a | a ≠ w}) (p : (G.induce {a | a ≠ w}).Walk u v) (hu : P u.1)
      (hv : P v.1), (G.induce (C : Set V)).Reachable (toC _ hu) (toC _ hv) := by
    intro u v p
    induction p with
    | nil => intro hu hv; exact Reachable.refl _
    | cons h p ih =>
      rename_i a b c
      intro hu hv
      have hb : P b.1 := hPclosed a b h hu
      exact (Adj.reachable (show (G.induce (C : Set V)).Adj (toC _ hu) (toC _ hb) from h)).trans
        (ih hb hv)
  have hCconn : (G.induce (C : Set V)).Connected := by
    refine ((G.induce _).connected_iff).mpr ⟨?_, ⟨toC x0 hx0P⟩⟩
    intro a b
    have ha := (hC a.1).mp (Finset.mem_coe.mp a.2)
    have hb := (hC b.1).mp (Finset.mem_coe.mp b.2)
    obtain ⟨h1, r1⟩ := ha
    obtain ⟨h2, r2⟩ := hb
    obtain ⟨p⟩ := r1.trans r2.symm
    exact claim _ _ p ⟨h1, r1⟩ ⟨h2, r2⟩
  have hcard : 2 ≤ C.card := by
    have hsub : ({x0, x0'} : Finset V) ⊆ C := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact (hC _).mpr hx0P
      · exact (hC _).mpr hx0'P
    have := Finset.card_le_card hsub
    rw [Finset.card_pair h00.ne] at this
    exact this
  refine ⟨C, L, ?_, ?_, ?_, ?_, hLne, hCconn, hcard, hLw, hLpend⟩
  · rw [Finset.disjoint_left]
    intro a ha hl
    exact ((hL a).mp hl).2 ((hC a).mp ha)
  · intro h
    exact ((hC w).mp h).1 rfl
  · intro h
    exact ((hL w).mp h).1 rfl
  · intro a ha
    by_cases hPa : P a
    · exact Or.inl ((hC a).mpr hPa)
    · exact Or.inr ((hL a).mpr ⟨ha, hPa⟩)

/-- Step 4, case (i), of D4: an end of the geodesic is pendant at `w`. -/
lemma step4_case_i (h3 : H3) (h4 : H4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (w l v : V) (hmax : ∀ u, G.degree u ≤ G.degree w) (hlw : G.Adj l w)
    (hl : ∀ c, G.Adj l c → c = w) (hdist : 3 ≤ G.dist w v)
    (hcore : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card = G.indepNum → v ∈ I) :
    G.residue + 1 ≤ G.indepNum := by
  have hvw : v ≠ w := by
    intro h
    rw [h, SimpleGraph.dist_self] at hdist
    omega
  have hvl : v ≠ l := by
    intro h
    rw [h] at hdist
    have : G.dist w l = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hlw.symm
    omega
  obtain ⟨b, hvb⟩ : ∃ b, G.Adj v b := by
    obtain ⟨p⟩ := hc.preconnected v w
    cases p with
    | nil => exact absurd rfl hvw
    | cons h _ => exact ⟨_, h⟩
  have htri := hc.dist_triangle (u := w) (v := b) (w := v)
  have hbv : G.dist b v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hvb.symm
  have hwb2 : 2 ≤ G.dist w b := by omega
  have hwb : ¬ G.Adj w b := fun h => by
    have := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  have hbw : b ≠ w := by
    intro h
    rw [h, SimpleGraph.dist_self] at hwb2
    omega
  refine residue_pendant_switch h3 h4 G w l v b hmax hlw hl hvw hvl hvb hwb hbw ?_
  intro t ht hav hcard
  have hlt : l ∉ t := fun h => (hav l h).2 rfl
  have hind : G.IsIndepSet ((insert l t : Finset V) : Set V) := by
    intro a ha c hc' hac hadj
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hc'
    rcases ha with rfl | ha <;> rcases hc' with rfl | hc'
    · exact hac rfl
    · exact (hav c hc').1 (hl c hadj)
    · exact (hav a ha).1 (hl a hadj.symm)
    · exact ht (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hc') hac hadj
  have hcard' : (insert l t).card = G.indepNum := by
    rw [Finset.card_insert_of_notMem hlt, hcard, indepNum_pendant G w l hlw hl]
  have := hcore _ hind hcard'
  rcases Finset.mem_insert.mp this with h | h
  · exact absurd h hvl
  · exact h

/-- Step 4, case (ii), of D4: both ends of the geodesic lie in the big component. -/
lemma step4_case_ii (h3 : H3) (h4 : H4) (n : ℕ)
    (IH : ∀ (W : Type) [Fintype W] [DecidableEq W] [Nontrivial W] (K : SimpleGraph W)
      [DecidableRel K.Adj], Fintype.card W < n → K.Connected → K.diam = 4 →
      K.residue + 2 ≤ K.largestInducedForestSize)
    (hn : Fintype.card V = n) (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) (C L : Finset V)
    (hwC : w ∉ C) (hwL : w ∉ L) (hdisj : Disjoint C L) (hcov : ∀ a, a ≠ w → a ∈ C ∨ a ∈ L)
    (hCc : (G.induce (C : Set V)).Connected) (hLpend : ∀ l ∈ L, ∀ b, G.Adj l b → b = w)
    (hmax : ∀ u, G.degree u ≤ G.degree w) (hedge : ∃ a b, G.Adj a b)
    (x y : V) (hx : x ∈ C) (hy : y ∈ C) (hxy : G.dist x y = 4)
    (hα : G.indepNum = (G.induce (C : Set V)).indepNum + L.card)
    (hF : G.largestInducedForestSize ≤ G.indepNum + 1) :
    G.residue + 1 ≤ G.indepNum := by
  have hxC : x ∈ (C : Set V) := Finset.mem_coe.mpr hx
  have hyC : y ∈ (C : Set V) := Finset.mem_coe.mpr hy
  have hdiamK : 4 ≤ (G.induce (C : Set V)).diam := by
    have := le_diam_induce G (C : Set V) hCc x y hxC hyC
    omega
  have hxy' : x ≠ y := by
    intro h
    rw [h, SimpleGraph.dist_self] at hxy
    omega
  haveI : Nontrivial ↥(C : Set V) :=
    ⟨⟨⟨x, hxC⟩, ⟨y, hyC⟩, fun h => hxy' (congrArg Subtype.val h)⟩⟩
  have hcardC : Fintype.card ↥(C : Set V) < n := by
    rw [← hn]
    have h1 : Fintype.card ↥(C : Set V) = C.card := by simp
    rw [h1]
    exact Finset.card_lt_univ_of_notMem hwC
  obtain ⟨s, hs, hscard⟩ := exists_forest_eq (G.induce (C : Set V))
  have hs' := forest_induce_map_acyclic G (C : Set V) s hs
  have hsub : (s.map (Function.Embedding.subtype _) : Finset V) ⊆ C := by
    intro a ha
    obtain ⟨a', _, rfl⟩ := Finset.mem_map.mp ha
    exact Finset.mem_coe.mp a'.2
  have hiso : ∀ l ∈ L, ∀ b ∈ (s.map (Function.Embedding.subtype _) : Finset V) ∪ L,
      ¬ G.Adj l b := by
    intro l hl b hb hadj
    have hbw := hLpend l hl b hadj
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hwC (hbw ▸ hsub hb)
    · exact hwL (hbw ▸ hb)
  have hU := isAcyclic_induce_union_isolated G _ L hs' hiso
  have hdisjL : Disjoint (s.map (Function.Embedding.subtype _) : Finset V) L :=
    Finset.disjoint_of_subset_left hsub hdisj
  have hF2 := card_le_forest G _ hU
  rw [Finset.card_union_of_disjoint hdisjL, Finset.card_map, hscard] at hF2
  by_cases hd4 : (G.induce (C : Set V)).diam = 4
  · have hK := IH ↥(C : Set V) (G.induce (C : Set V)) hcardC hCc hd4
    have h4' := h4 V G w hedge hmax
    have hset : {a | a ≠ w} \ (L : Set V) = (C : Set V) := by
      ext a
      simp only [Set.mem_diff, Set.mem_setOf_eq, Finset.mem_coe]
      constructor
      · rintro ⟨hne, hnL⟩
        exact (hcov a hne).resolve_right hnL
      · intro ha
        exact ⟨fun h => hwC (h ▸ ha), fun h => Finset.disjoint_left.mp hdisj ha h⟩
    have hLsub : (L : Set V) ⊆ {a | a ≠ w} := by
      intro a ha
      exact fun h => hwL (h ▸ Finset.mem_coe.mp ha)
    have hiso2 : ∀ l ∈ L, ∀ b ∈ ({a | a ≠ w} : Set V), ¬ G.Adj l b := by
      intro l hl b hb hadj
      exact hb (hLpend l hl b hadj)
    have hres0 := residue_induce_isolated G {a | a ≠ w} (C : Set V) L hLsub hiso2 hset.symm
    have hres : (G.induce {a | a ≠ w}).residue = (G.induce (C : Set V)).residue + L.card := by
      convert hres0
    omega
  · have h5 := indepNum_add_le_forest (G.induce (C : Set V)) hCc
    omega

/-- The induction step of D4. -/
lemma d4_step (h3 : H3) (h4 : H4) (n : ℕ)
    (IH : ∀ (W : Type) [Fintype W] [DecidableEq W] [Nontrivial W] (K : SimpleGraph W)
      [DecidableRel K.Adj], Fintype.card W < n → K.Connected → K.diam = 4 →
      K.residue + 2 ≤ K.largestInducedForestSize)
    [Nontrivial V] (hn : Fintype.card V = n) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hd : G.diam = 4) :
    G.residue + 2 ≤ G.largestInducedForestSize := by
  by_contra hlt
  have hF : G.largestInducedForestSize ≤ G.residue + 1 := by omega
  have h1 := indepNum_succ_le_forest G hc
  have h2 := h3 V G
  have hRα : G.residue = G.indepNum := by omega
  have hF' : G.largestInducedForestSize ≤ G.indepNum + 1 := by omega
  obtain ⟨w, -, hw⟩ := Finset.exists_max_image Finset.univ (fun v => G.degree v)
    ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hmax : ∀ v, G.degree v ≤ G.degree w := fun v => hw v (Finset.mem_univ _)
  have hedge := exists_adj_of_connected G hc
  obtain ⟨I, hIind, hIcard, hwI⟩ := exists_max_indep_avoid h3 h4 G w hedge hmax hRα
  obtain ⟨x, y, hxy⟩ := G.exists_dist_eq_diam
  rw [hd] at hxy
  have hcore : ∀ I' : Finset V, G.IsIndepSet (I' : Set V) → I'.card = G.indepNum →
      x ∈ I' ∧ y ∈ I' := fun I' hI' hc' => core_endpoints G hc hF' I' hI' hc' x y hxy
  have hcore' : ∀ I' : Finset V, G.IsIndepSet (I' : Set V) → I'.card = G.indepNum →
      y ∈ I' ∧ x ∈ I' := fun I' hI' hc' => (hcore I' hI' hc').symm
  have hxw : x ≠ w := fun h => hwI (h ▸ (hcore I hIind hIcard).1)
  have hyw : y ≠ w := fun h => hwI (h ▸ (hcore I hIind hIcard).2)
  by_cases hconn : (G.induce {a | a ≠ w}).Connected
  · have := step2 h3 h4 n IH hn G w hedge hmax hconn x y hxw hyw hxy
    omega
  · obtain ⟨C, L, hdisj, hwC, hwL, hcov, hLne, hCc, hC2, hLw, hLpend⟩ :=
      step3_structure G hc hd w hF' ⟨I, hIind, hIcard, hwI⟩ hconn
    have hα := indepNum_split G w C L hwC hwL hdisj hcov hLpend ⟨I, hIind, hIcard, hwI⟩
    have key_i : ∀ l v : V, l ∈ L → G.dist l v = 4 →
        (∀ I' : Finset V, G.IsIndepSet (I' : Set V) → I'.card = G.indepNum → v ∈ I') → False := by
      intro l v hl hlv hcv
      have hlw := hLw l hl
      have htri := hc.dist_triangle (u := l) (v := w) (w := v)
      have h1 : G.dist l w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hlw
      have := step4_case_i h3 h4 G hc w l v hmax hlw (hLpend l hl) (by omega) hcv
      omega
    rcases hcov x hxw with hxC | hxL <;> rcases hcov y hyw with hyC | hyL
    · have := step4_case_ii h3 h4 n IH hn G w C L hwC hwL hdisj hcov hCc hLpend hmax hedge x y
        hxC hyC hxy hα hF'
      omega
    · exact key_i y x hyL (by rw [SimpleGraph.dist_comm]; exact hxy)
        (fun I' hI' hc' => (hcore I' hI' hc').1)
    · exact key_i x y hxL hxy (fun I' hI' hc' => (hcore I' hI' hc').2)
    · have hxw' := hLw x hxL
      have hyw' := hLw y hyL
      have htri := hc.dist_triangle (u := x) (v := w) (w := y)
      have e1 : G.dist x w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxw'
      have e2 : G.dist w y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyw'.symm
      omega

end d4_lemmas

/-- Theorem D4: a connected graph of diameter four satisfies `residue + 2 ≤ f`. -/
theorem d4 (h3 : H3) (h4 : H4) :
    ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
      [DecidableRel G.Adj], Fintype.card V = n → G.Connected → G.diam = 4 →
      G.residue + 2 ≤ G.largestInducedForestSize := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ G _ hn hc hd
    exact d4_step h3 h4 n
      (fun W _ _ _ K _ hlt hKc hKd => ih (Fintype.card W) hlt W K rfl hKc hKd) hn G hc hd

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_WrittenOnTheWallII_GraphConjecture61_conjecture61_R1.H2 := by
  intro h1 h2 h3 h4 V _ _ _ G _ hc hd hgap
  by_cases h4d : G.diam = 4
  · have hD := d4 h3 h4 _ V G rfl hc h4d
    have hceil : ⌈(G.diam : ℝ) / 3⌉ = 2 := by
      rw [h4d, Int.ceil_eq_iff]
      norm_num
    rw [hceil]
    exact_mod_cast hD
  · by_cases h15 : G.diam ≤ 15
    · exact h1 V G hc ⟨by omega, h15⟩ hgap
    · exact h2 V G hc (by omega) hgap

end OMA.R_WrittenOnTheWallII_GraphConjecture61_conjecture61_R1_H2_R1

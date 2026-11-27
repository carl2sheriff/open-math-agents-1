# Blueprint — Théorèmes D, D⁺, D⁺⁺ (WOWII 189, 2σ+3 ≤ n ≤ 2σ+6), cadre x₀-plus long

Cible : `reductions/WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2.R1.lean`,
`import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2`,
namespace `OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1`.
Sources : research-189.md (§0, §2, H1, H2, Manche 2) + verif-D.md (E1, diamant, trou K₄ σ=4). **Toutes les
corrections de verif-D sont intégrées** (B'_y partout ; C₄/diamant réécrits ; écart croisé justifié en K₄ σ=4).

## 0. Conventions, cadre, choix de preuve

### 0.1 Notations
- n = |V|, σ = `secondSmallestDegree G`, (H) : |Γ(v)| ≤ σ où Γ(v) = {w ≠ v : d(v,w) pair} (`distEven = 1 + |Γ|`).
- x₀ : sommet de degré minimum. Fait 0 : v ≠ x₀ ⇒ deg v ≥ σ (`degree_pair`, R2).
- P = `l`, m = `l.length`. **Maths 1-indexées** (x₁…x_m) ; **Lean 0-indexé** : `x i := l.getD i x₀`
  (x_k maths = `x (k-1)` Lean). Le défaut x₀ est sans danger : toujours accompagné de `i < m`.
- R = `Rset l := Finset.univ.filter (· ∉ l)`, |R| = n − m. Pour y ∈ R : J(y) = indices des voisins de y sur P,
  c(y) = |J(y)|, k(y) = |N(y) ∩ R|, deg y = c(y) + k(y).
- D(y) = J(y)±1 (indices), T(y) = {j ∈ J(y) : j+2 ∈ J(y)} (« trous » x_{j+1} de y), t(y) = |T(y)|.
- **B'_y = N_P(N_R(y)) \ N_P(y)** (correction E1 ; *jamais* N_P(R \ {y})). K₂(y) = {w ∈ R : d(y,w) = 2}.
- A = N_P(R) (indices a₁ < … < a_r), « régions » : gauche x₁..x_{a₁−1}, écarts entre attaches consécutives,
  droite x_{a_r+1}..x_m. Un écart (a, a') est **croisé** s'il existe y ≠ y' dans R avec y ~ x_a, y' ~ x_{a'}.
- i₀ = indice de x₀ sur P ; 0 < i₀ < m−1 (Lean) car les extrémités sont ≠ x₀.

### 0.2 Le cadre (hypothèses communes, structure Lean)
```lean
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure Cadre (G : SimpleGraph V) [DecidableRel G.Adj] (x₀ : V) (l : List V) : Prop where
  conn  : G.Connected
  bicon : ∀ c : V, (G.induce {x | x ≠ c}).Connected
  hH    : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G
  hmin  : ∀ v, G.degree x₀ ≤ G.degree v
  hx0   : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v
  hδ    : ∀ v, 2 ≤ G.degree v
  ne    : l ≠ []
  nd    : l.Nodup
  ch    : l.IsChain G.Adj
  mem   : x₀ ∈ l
  head  : l.head ne ≠ x₀
  last  : l.getLast ne ≠ x₀
  max   : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length
  lt    : l.length < Fintype.card V
```
Plus `[Nontrivial V]` en argument d'instance. Toutes les lemmes B5–B24 prennent `(hC : Cadre G x₀ l)`.

### 0.3 Trois choix qui raccourcissent la preuve (par rapport à research-189)
1. **2-connexité utilisée directement** (hypothèse de R2.H2) : remplace le Lemme 6a dans (R4), (R6) et E′ (c=1).
   Un seul outil : B4 `cut_closed`.
2. **(Q3) sous forme globale** (B11) : *tout sommet de R a ≥ 2 voisins dans R*. Donc |R| ≥ 3 : le Théorème D
   (|R| ≤ 2) devient immédiat, et pour |R| = 3 (resp. 4) G[R] = K₃ (resp. C₄, diamant, K₄) sans parler de
   composantes : R est **une seule** « composante » K = R, fermée par définition.
3. **Cas concrets** (σ = 4, 5) : soit un lemme générique en indices (B17 trou-x₀, B18 x₀-attache,
   B19 marche-x₀), soit un comptage de degré d'extrémité (B20) avec m numéral. Les miroirs passent par
   B1 `Cadre.reverse` (indice i ↦ m−1−i).

### 0.4 Squelette global
n ≥ 2σ+3 ⇒ δ ≥ 2 (h11). Si un chemin contenant x₀ a n sommets : `ham_of_list`. Sinon h18 donne l (cadre).
B12 : m ≥ 2σ+2, donc |R| ≤ n − 2σ − 2 ≤ 4. B11 : |R| ≥ 3. Restent :
- |R| = 3, m = 2σ+2 (n = 2σ+5, **D⁺**) et |R| = 3, m = 2σ+3 (n = 2σ+6, **D⁺⁺ cas B**) : B21–B22 ;
- |R| = 4, m = 2σ+2 (n = 2σ+6, **D⁺⁺ cas A**) : B23 (non-clique = C₄/diamant) et B24 (K₄).
**D** (n ≤ 2σ+4) : |R| ≤ 2 < 3, contradiction immédiate (B14).

---

## 1. Socle (Lot 1)

### B1 — Cadre, copies, miroir
**Énoncé.** (a) `Cadre.hmax_sup` : ∀ l', Nodup → IsChain → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length.
(b) `Cadre.reverse : Cadre G x₀ l → Cadre G x₀ l.reverse` ; `getD_reverse : i < m → l.reverse.getD i d = l.getD (m-1-i) d`.
(c) Construction : sous H := (connexe, 2-connexe, (H), 2σ+3 ≤ n, x₀ argmin du degré), ou bien ∃ chemin hamiltonien,
ou bien ∃ l, `Cadre G x₀ l`.
**Preuve.** (a) x₀ ∈ l ⊆ l'. (b) Nodup/IsChain/longueur/appartenance invariants par renversement, head ↔ getLast.
(c) h11 (δ ≥ 2) ; `by_cases` « tout chemin contenant x₀ a < n sommets » comme dans `H1Aux.main` ; h18.
**Réutilise (copier depuis proofs/…R2.H1.lean, non importable)** : `Closed`, `h11`, `sigma_ge`, `lemma4x`,
`longer_of_perm_x`, `no_insert_x`, `lemma5abx`, `exists_longest_x0`, `chain_rev`, `rot_head`, `h18`.
**Importé de R2** : `degree_pair`, `ham_of_list`, `dist_two`, `lemma3a`, `lemma3b`, `exists_out_edge`, `getD_zero`, `getD_last`.
**Taille** : copie ≈ 550 lignes ; neuf ≈ 80.

### B2 — deg x₀ ≤ σ
`lemma deg_x0_le [Nontrivial V] (hmin : ∀ v, G.degree x₀ ≤ G.degree v) : G.degree x₀ ≤ secondSmallestDegree G`
**Preuve.** σ = `(degreeSequence G).getD 1 0` est un élément de la suite triée (longueur ≥ 2), donc = deg v pour un v ;
deg x₀ ≤ deg v. Sert à B18 et à `minDegree ≤ σ` (B26). **Taille** 40.

### B3 — Comptage de Γ
`lemma card_le_gamma (hconn) (hH) (v : V) (S : Finset V) (hS : ∀ w ∈ S, G.dist v w = 2) : S.card ≤ secondSmallestDegree G`
**Preuve.** S ⊆ (univ.filter (Even ∘ dist v)).erase v, de cardinal `distEven G v − 1 ≤ σ`.
Usage type : exhiber σ+1 sommets distincts à distance 2 (chacun par `dist_two` : v ~ a ~ w, v ≁ w, w ≠ v). **Taille** 30.

### B4 — Coupure (2-connexité)
`lemma cut_closed (hb : ∀ c, (G.induce {x | x ≠ c}).Connected) (c : V) (S : Finset V) (hc : c ∉ S) (hS : S.Nonempty)
  (hcl : ∀ v ∈ S, ∀ w, G.Adj v w → w ≠ c → w ∈ S) (hout : ∃ w, w ≠ c ∧ w ∉ S) : False`
**Preuve.** Marche dans `G.induce {x ≠ c}` de s ∈ S vers w ; image dans G (support évite c) ; `Walk.exists_boundary_dart`
pour {x ∈ S} donne une arête v ~ w' avec v ∈ S, w' ∉ S, w' ≠ c : contredit hcl. (Même schéma que `exists_out_edge`.)
**Taille** 60.

### B5 — Chirurgie de chemin (outil universel)
Tous les « chemin plus long contenant x₀ » du texte sont des instances de ces quatre lemmes ou de listes explicites.
```lean
lemma Cadre.no_longer (hC) (l' : List V) (h1 : l'.Nodup) (h2 : l'.IsChain G.Adj) (h3 : x₀ ∈ l')
    (h4 : l.length < l'.length) : False
lemma Cadre.no_mid (hC) (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj)
    (sl : ∀ v ∈ s, v ∉ l) (a b : ℕ) (hab : a < b) (hb : b < l.length)
    (h1 : G.Adj (l.getD a x₀) (s.head hs)) (h2 : G.Adj (s.getLast hs) (l.getD b x₀))
    (hx : ∀ i, a < i → i < b → l.getD i x₀ ≠ x₀) (hlen : b - a - 1 < s.length) : False
lemma Cadre.no_pre (hC) (s …) (a : ℕ) (ha : a < l.length) (h : G.Adj (s.getLast hs) (l.getD a x₀))
    (hx : ∀ i < a, l.getD i x₀ ≠ x₀) (hlen : a < s.length) : False
lemma Cadre.no_suf (hC) (s …) (b : ℕ) (hb : b < l.length) (h : G.Adj (l.getD b x₀) (s.head hs))
    (hx : ∀ i, b < i → i < l.length → l.getD i x₀ ≠ x₀) (hlen : l.length - 1 - b < s.length) : False
```
**Preuve.** no_mid : l' = l.take (a+1) ++ s ++ l.drop b ; Nodup (s disjoint de l ; take/drop disjoints) ; IsChain
(`List.isChain_append` aux deux jonctions) ; x₀ ∈ take ∪ drop par hx ; |l'| = m + |s| − (b−a−1) > m.
no_pre : l' = s ++ l.drop a. no_suf : `no_pre` appliqué à `hC.reverse` et `s.reverse`.
**Couvre** : Lemme P(a) (insertion de [y,z]), (Q1)(i)(ii) régions, trous de E′, privauté (B23).
**Taille** no_longer 5, no_mid 130, no_pre 60, no_suf 40.

### B6 — Astuce d'extrémité (E)
```lean
lemma Cadre.endE (hC) (s : List V) (hs …) (snd sch sl) (a j : ℕ) (haj : a < j) (hj : j < l.length)
    (h1 : G.Adj (l.getD 0 x₀) (l.getD j x₀)) (h2 : G.Adj (s.getLast hs) (l.getD a x₀))
    (hx : ∃ i, (i ≤ a ∨ j ≤ i) ∧ i < l.length ∧ l.getD i x₀ = x₀) (hlen : j - a ≤ s.length) : False
lemma Cadre.endE_last … -- version pour x_m, par hC.reverse
```
**Énoncé maths.** Si x₁ ~ x_j (j > a) et K a un chemin s finissant en un voisin de x_a, le chemin
s, x_a, x_{a−1}, …, x₁, x_j, …, x_m a |s| + a + m − j + 1 sommets (maths) ; s'il contient x₀ et dépasse m : contradiction.
**Preuve.** l' = s ++ (l.take (a+1)).reverse ++ l.drop j ; jonctions : s.last ~ x_a, x₁ ~ x_j. **Taille** 90 + 30.

---

## 2. Comptage et structure de R (Lot 2)

### B7 — Anneau d'indices (pur ℕ)
```lean
def Jset (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V) (x₀ y : V) : Finset ℕ :=
  (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))
def Dset G l x₀ y : Finset ℕ := (Jset G l x₀ y).image (· + 1) ∪ (Jset G l x₀ y).image (· - 1)
def Tset G l x₀ y : Finset ℕ := (Jset G l x₀ y).filter (fun j => j + 2 ∈ Jset G l x₀ y)
def Rset (l : List V) : Finset V := Finset.univ.filter (· ∉ l)

lemma ring_card (J : Finset ℕ) (h0 : 0 ∉ J) :
    (J.image (· + 1) ∪ J.image (· - 1)).card + (J.filter (· + 2 ∈ J)).card = 2 * J.card
lemma T_lt (J : Finset ℕ) (hJ : J.Nonempty) : (J.filter (· + 2 ∈ J)).card + 1 ≤ J.card
lemma prog (J : Finset ℕ) (hJ : J.Nonempty) (ht : (J.filter (· + 2 ∈ J)).card + 1 = J.card) :
    (∀ j ∈ J, j ≠ J.max' hJ → j + 2 ∈ J) ∧ (∀ j ∈ J, j ≠ J.min' hJ → 2 ≤ j ∧ j - 2 ∈ J)
```
**Maths.** |J+1 ∪ J−1| = 2c − t (l'intersection est (T)+1) ; t ≤ c − 1 (max J ∉ T) ; t = c − 1 ⇔ J progression de pas 2.
**Preuve.** ring_card : `card_union_add_card_inter`, injectivité de ·+1 et de ·−1 sur J (0 ∉ J), X ∩ Y = T.image (·+1).
T_lt : T ⊆ J.erase max'. prog : T = J.erase max' (inclusion + cardinal) puis T.image (·+2) ⊆ J.erase min', même cardinal.
**Taille** 150.

### B8 — Distances 2 de l'anneau, décomposition du degré
```lean
lemma Cadre.J_bounds (hC) {y} (hy : y ∉ l) {j} (hj : j ∈ Jset G l x₀ y) : 0 < j ∧ j + 1 < l.length
lemma Cadre.dset_dist (hC) {y} (hy : y ∉ l) {i} (hi : i ∈ Dset G l x₀ y) :
    i < l.length ∧ G.dist y (l.getD i x₀) = 2
lemma Cadre.degree_split (hC) {y} (hy : y ∉ l) :
    G.degree y = (Jset G l x₀ y).card + ((Rset l).filter (G.Adj y)).card
```
**Preuve.** J_bounds, dset_dist : `lemma5abx` (0 < j, j+1 < m, y ≁ x_{j±1}) + `dist_two`. degree_split : neighborFinset =
image de Jset par `l.getD · x₀` (injective sur range m, Nodup) ⊔ voisins dans R. **Taille** 90.

### B9 — Lemme P corrigé / (Q2) avec B'_y
**Énoncé maths.** y ∈ R, c(y) ≥ 1. Alors x(D(y)), B'_y, K₂(y) sont disjoints et inclus dans Γ(y) ; d'où
**2c(y) − t(y) + |B'_y| + |K₂(y)| ≤ σ**, avec 2c − t ≥ c + 1. (Sous Fait 0 : σ ≤ c(y) + k(y).)
**Preuve.** x(D(y)) ⊆ Γ(y) : B8. w ∈ B'_y : w ~ z ~ y, w ≁ y ⇒ d = 2. K₂ : par définition. Disjonction : D, B' ⊆ P et
K₂ ⊆ R. x(D) ∩ B' = ∅ : si z ∈ N_R(y) voit x_{j+1} avec y ~ x_j, alors x_j y z x_{j+1} insère deux sommets
(B5 `no_mid`, s = [y,z], b = a+1) ; cas x_{j−1} : s = [z,y]. (C'est exactement là que l'ancienne définition
B_y = N_P(K \ {y}) \ N_P(y) cassait : un sommet de K non voisin de y peut être à distance 3 — E1.)
```lean
lemma Cadre.count_Q2 (hC) (y : V) (hy : y ∉ l) (Bp K2 : Finset V)
    (hB : ∀ w ∈ Bp, w ∈ l ∧ ¬ G.Adj y w ∧ ∃ z, z ∉ l ∧ G.Adj y z ∧ G.Adj z w)
    (hK : ∀ w ∈ K2, w ∉ l ∧ w ≠ y ∧ ¬ G.Adj y w ∧ ∃ z, G.Adj y z ∧ G.Adj z w) :
    (Dset G l x₀ y).card + Bp.card + K2.card ≤ secondSmallestDegree G
```
**Dépend** : B3, B5, B8. **Taille** 160.

### B10 — Lemme E′ (pas de composante arête)
**Énoncé.** Pas de y, z ∈ R avec y ~ z, N_R(y) = {z}, N_R(z) = {y}.
**Preuve.** c(y) = deg y − 1 ≥ σ − 1 ≥ 1 (σ ≥ 2 : `sigma_ge`). B9 (B' = (N_P(z) \ N_P(y)), K₂ = ∅) :
2c − t + |B'_y| ≤ σ ≤ c + 1 ≤ 2c − t ⇒ B'_y = ∅, t = c − 1, σ = c + 1. Donc N_P(z) ⊆ N_P(y) ; symétriquement
(rôle de z) N_P(y) ⊆ N_P(z) : J(y) = J(z) =: J.
Trous : j ∈ T ⇒ x_{j+1} = x₀ (sinon B5 `no_mid` avec s = [y,z], y ~ x_j, z ~ x_{j+2}). Donc T ⊆ {i₀ − 1}, t ≤ 1,
c ≤ 2, σ = c + 1 ≤ 3.
- σ = 2 (c = 1, J = {p}) : S = {y,z} est fermé dans G − x_p (deg y = deg z = 2) ; B4 (`hout` : x₁). ✗
- σ = 3 (c = 2, J = {p, p+2}, x_{p+1} = x₀) : B17 `hole_x0` avec K = {y,z}, s = [y,z] : |K| + 2 = 4 ≤ σ = 3. ✗
```lean
lemma Cadre.no_edge_comp (hC) (y z : V) (hy : y ∉ l) (hz : z ∉ l) (hyz : G.Adj y z)
    (hNy : ∀ w, w ∉ l → G.Adj y w → w = z) (hNz : ∀ w, w ∉ l → G.Adj z w → w = y) : False
```
**Dépend** : B4, B5, B7, B9, B17. **Taille** 200.

### B11 — (Q3) global : tout sommet de R a ≥ 2 voisins dans R
```lean
lemma Cadre.Rdeg2 (hC) (y : V) (hy : y ∉ l) : 2 ≤ ((Rset l).filter (G.Adj y)).card
```
**Preuve.** y ≠ x₀ (x₀ ∈ l) ⇒ deg y ≥ σ ≥ 2.
- k = 0 : c = deg y ≥ 2 ; B9 (B' = K₂ = ∅) : c + 1 ≤ |D| ≤ σ ≤ c. ✗ (c'est le Lemme 5c, version x₀).
- k = 1, N_R(y) = {z} : c = deg y − 1 ≥ 1. Si w ∈ R \ {y}, w ~ z, alors w ≁ y, d(y,w) = 2 : B9 avec K₂ = {w} :
  c + 2 ≤ σ ≤ c + 1. ✗ Donc N_R(z) = {y} : B10. ✗
**Dépend** : B8, B9, B10. **Taille** 100.

### B12 — (R4) dans le cadre : m ≥ 2σ+2
```lean
lemma Cadre.m_ge (hC) : 2 * secondSmallestDegree G + 2 ≤ l.length
```
**Preuve.** `lemma4x` : N(x₁), N(x_m) ⊆ P, deg x₁ + deg x_m + 1 ≤ m, extrémités ≠ x₀ ⇒ m ≥ 2σ+1. Supposons m = 2σ+1.
Alors deg x₁ = deg x_m = σ et I₁ ⊔ I_m = [1, m−1] (4e composante de lemma4x : disjonction ; cardinaux).
(i) y ∈ R, y ~ x_j ⇒ x₁ ~ x_j (5b : j−1 ∉ I_m ⇒ j−1 ∈ I₁), donc d(x₁, y) = 2.
(ii) |V \ N[x₁]| = |R| + σ ; `lemma3b` ⇒ |F(x₁)| ≥ |R| (F = distance impaire ≥ 3).
(iii) w ∈ F(x₁) ∩ P : N(w) ∩ N[x₁] = ∅ (`lemma3a`), w n'a pas de voisin dans R (sinon (i) donne x₁ ~ w) ⇒
N(w) ⊆ (P \ N[x₁]) \ {w}, deg w ≤ σ − 1 ⇒ w = x₀. (iv) w ∈ F(x₁) ∩ R ⇒ w sans voisin sur P (par (i)).
(v) R₀ := {y ∈ R sans voisin sur P}, R₁ := R \ R₀ ≠ ∅ (`exists_out_edge`). |R| ≤ |F| ≤ 1 + |R₀| ⇒ R₁ = {y₁}.
Si R₀ ≠ ∅ : R₀ est fermé dans G − y₁ ⇒ B4. ✗ Si R₀ = ∅ : |R| = 1 contredit B11. ✗
**Adapter** `caseA` de R2 (l. 843–1068 : mêmes étapes A3–A6, avec R quelconque). **Dépend** : B4, B11. **Taille** 320.

### B13 — (R6) : au moins deux attaches
```lean
lemma Cadre.two_attach (hC) : ∃ a b, a < b ∧ b < l.length ∧
    (∃ y ∈ Rset l, G.Adj y (l.getD a x₀)) ∧ (∃ y ∈ Rset l, G.Adj y (l.getD b x₀))
```
**Preuve.** R ≠ ∅ (m < n) ; une attache x_a existe (`exists_out_edge`). Si c'est la seule : R est fermé dans G − x_a
(un voisin hors R d'un sommet de R est une attache, donc x_a) ; `hout` : x₁ (a ≥ 1). B4. ✗ **Taille** 60.

### B14 — Théorème D et forme de R
```lean
lemma Cadre.R_ge3 (hC) : 3 ≤ (Rset l).card
lemma Cadre.R_card (hC) : (Rset l).card + l.length = Fintype.card V
lemma Cadre.R3 (hC) (h : (Rset l).card = 3) : ∃ u v w, Rset l = {u, v, w} ∧ u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
    G.Adj u v ∧ G.Adj v w ∧ G.Adj u w
lemma Cadre.R4 (hC) (h : (Rset l).card = 4) :
    (∃ a b c d, Rset l = {a,b,c,d} ∧ [6 distinctions] ∧ [6 adjacences]) ∨
    (∃ z z' a b, Rset l = {z,z',a,b} ∧ [6 distinctions] ∧ ¬ G.Adj z z' ∧
       G.Adj z a ∧ G.Adj z b ∧ G.Adj z' a ∧ G.Adj z' b)
```
**Preuve.** R ≠ ∅, y ∈ R a 2 voisins dans R (B11) ⇒ |R| ≥ 3. |R| = 3 : chacun voit les deux autres. |R| = 4 : si R
n'est pas une clique, soit z ≁ z' ; chacun a ≥ 2 voisins dans R \ {z,z'} = {a,b}. (a ~ b : diamant ; a ≁ b : C₄ ;
**inutile de distinguer** : la preuve B23 n'utilise que les 4 arêtes z–a, z–b, z'–a, z'–b.)
**Théorème D** (n ≤ 2σ+4) : B12 ⇒ |R| ≤ 2, contredit R_ge3. **Taille** 150.

---

## 3. Régions, empilement, lemmes locaux autour de x₀ (Lot 3)

### B15 — Borne générique des petits σ (régions extrêmes + un écart)
**Énoncé.** Si tout sommet de R est l'extrémité d'un chemin hamiltonien de G[R] et si G[R] est de diamètre ≤ 2,
alors **m ≥ |R| + 5**.
**Preuve.** a₁ = min A, a_r = max A (B13 : a₁ < a_r). Gauche : `no_pre` avec un chemin hamiltonien de R finissant en
un voisin de x_{a₁} ⇒ a₁ − 1 ≥ |R| ou x₀ à gauche (alors a₁ − 1 ≥ 2 car x₁ ≠ x₀). Droite : idem (`no_suf`).
Pas les deux à la fois. Milieu : a_r ≥ a₁ + 2, sinon x_{a₁}, x_{a₁+1} consécutifs, porteurs y, y' : y = y' ⇒
insertion [y] ; y ≠ y' ⇒ insertion [y,y'] ou [y,w,y'] (`no_mid`). Somme : m ≥ |R| + 2 + 3.
```lean
lemma Cadre.small_sigma (hC)
    (hham : ∀ y ∈ Rset l, ∃ s : List V, s.Nodup ∧ s.IsChain G.Adj ∧ s.toFinset = Rset l ∧ s.getLast? = some y)
    (hd2 : ∀ y ∈ Rset l, ∀ y' ∈ Rset l, y ≠ y' → G.Adj y y' ∨ ∃ w ∈ Rset l, G.Adj y w ∧ G.Adj w y') :
    (Rset l).card + 5 ≤ l.length
```
**Usage** : K₃, σ = 2 (m ≥ 8 > 2σ+3) ; |R| = 4, σ ≤ 3 (m ≥ 9 > 2σ+2). Chemins fournis par l'appelant :
K₃ [v,w,y] ; K₄ tout ordre ; non-clique (z,z',a,b) : fin en z [b,z',a,z], en z' [b,z,a,z'], en a [z,b,z',a], en b [z,a,z',b].
**Dépend** : B5, B13. **Taille** 130.

### B16 — Empilement des régions (pur ℕ)
**Énoncé maths.** r attaches, r+1 régions ; chaque région a ≥ k sommets sauf celle de x₀ (≥ 1) et les écarts
« exceptionnels » E (≥ 1). Alors m ≥ (k+1)r + 1 − (k−1)|E|.
```lean
lemma pack (A E : Finset ℕ) (m k i₀ : ℕ) (hk : 1 ≤ k) (hA : A.Nonempty) (hE : E ⊆ A)
    (hAm : ∀ a ∈ A, 1 ≤ a ∧ a + 2 ≤ m) (hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ m)
    (hL : k ≤ A.min' hA ∨ i₀ < A.min' hA)
    (hR : A.max' hA + k + 1 ≤ m ∨ A.max' hA < i₀)
    (hM : ∀ a ∈ A, ∀ b ∈ A, a < b → (∀ c ∈ A, ¬ (a < c ∧ c < b)) →
        a + 2 ≤ b ∧ (a ∉ E → a + k + 1 ≤ b ∨ (a < i₀ ∧ i₀ < b))) :
    (k + 1) * A.card + 1 ≤ m + (k - 1) * E.card
```
**Preuve (indication).** `Finset.induction_on_max`, invariant
(k+1)·|A| ≤ max A + 1 + (k−1)·(|E ∩ A.erase (max A)| + [i₀ < max A]).
Base {a} : hL. Pas (on ajoute b > max A = a, consécutifs) : il faut b − a + (k−1)([a ∈ E] + [a ≤ i₀ < b]) ≥ k+1, ce que
donne hM (trois cas). Fin : hR (si x₀ est à droite, le terme [i₀ < max] vaut 0 et la droite compte ≥ 1).
**Usage** : K₃ (k = 3, E = ∅) : **m ≥ 4r + 1** ; K₄ (k = 4, |E| ≤ 1) : **m ≥ 5r − 2** ; K₄ tous voient A (E = ∅) : m ≥ 5r + 1.
**Taille** 180 (indépendant de tout le reste).

### B17 — x₀ seul dans un écart d'un sommet (« trou-x₀ »)
**Énoncé maths.** x₀ = x_{p+1}, S ⊆ R avec tout y ∈ S voisin de x_p ou de x_{p+2}, et un chemin s ⊆ R allant d'un
voisin de x_p à un voisin de x_{p+2}. Alors x₀ ≁ x_{p−1}, x₀ ≁ x_{p+3} et **|S| + 2 ≤ σ**.
**Preuve.** x₀ ~ x_{p−1} : x₁…x_{p−1} x₀ x_p s x_{p+2}…x_m (m + |s| sommets). x₀ ~ x_{p+3} : x₁…x_p s x_{p+2} x₀ x_{p+3}…x_m.
Donc S ∪ {x_{p−1}, x_{p+3}} ⊆ L₂(x₀) (y ≁ x₀ par 5a, x₀ étant voisin sur P d'une attache de y) ; B3.
```lean
lemma Cadre.hole_x0 (hC) (S : Finset V) (hS : ∀ y ∈ S, y ∉ l) (p : ℕ) (hp : 1 ≤ p) (hp3 : p + 3 < l.length)
    (hx : l.getD (p + 1) x₀ = x₀)
    (hSA : ∀ y ∈ S, G.Adj y (l.getD p x₀) ∨ G.Adj y (l.getD (p + 2) x₀))
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l)
    (h1 : G.Adj (l.getD p x₀) (s.head hs)) (h2 : G.Adj (s.getLast hs) (l.getD (p + 2) x₀)) :
    S.card + 2 ≤ secondSmallestDegree G
```
Listes Lean : `l.take p ++ [x₀, l.getD p x₀] ++ s ++ l.drop (p+2)` et `l.take (p+1) ++ s ++ [l.getD (p+2) x₀, x₀] ++ l.drop (p+3)`.
**Usage** : E′ σ=3 (4 ≤ 3), K₃ σ=3,4 (5 ≤ σ), K₄ σ=5 (6 ≤ 5), D⁺ σ=4 cas (a). **Taille** 150.

### B18 — x₀ est une attache
```lean
lemma Cadre.x0_attach (hC) (S : Finset V) (hS : ∀ y ∈ S, y ∉ l) (p : ℕ) (hp : 1 ≤ p) (hp1 : p + 1 < l.length)
    (hx : l.getD p x₀ = x₀) (hSA : ∀ y ∈ S, G.Adj y x₀) : S.card + 2 ≤ secondSmallestDegree G
```
**Preuve.** N(x₀) ⊇ S ⊔ {x_{p−1}, x_{p+1}} et deg x₀ ≤ σ (B2). **Usage** : K₃ σ=4 (5 ≤ 4), K₄ σ=5 (6 ≤ 5). **Taille** 40.

### B19 — Marche de x₀ dans un écart court (« marche-x₀ »)
**Énoncé maths.** x₀ = x_{p+1}, q ≥ p+3, chaque sommet d'un chemin s ⊆ R voit x_p et x_q, σ ≤ |s| + 1 et
g := q − p − 1 ≤ |s|. Contradiction.
**Preuve.** (1) x₀ ≁ x_{p−1} : x₁…x_{p−1} x₀ x_p s x_q…x_m a m − (g−1) + |s| > m sommets.
(2) Γ(x₀) ⊇ s ∪ {x_{p−1}} (distance 2 via x_p ; s ≁ x₀ par 5a) : déjà ≥ σ éléments.
(3) Pour i = p+3, …, q+1 : x₀ ~ x_{i−1} (hérédité ; base x₀ ~ x_{p+2} sur P) ; si x₀ ≁ x_i, x_i ∈ L₂(x₀) est un
(σ+1)-ième élément (B3). Donc x₀ ~ x_i.
(4) i = q+1 : x₁…x_p s x_q x_{q−1}…x_{p+1} x_{q+1}…x_m a m + |s| sommets. ✗
Liste Lean de (4) : `l.take (p+1) ++ s ++ ((l.drop (p+1)).take (q-p)).reverse ++ l.drop (q+1)`.
```lean
lemma Cadre.walk_x0 (hC) (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l)
    (p q : ℕ) (hp : 1 ≤ p) (hpq : p + 3 ≤ q) (hq : q + 1 < l.length) (hx : l.getD (p + 1) x₀ = x₀)
    (hsp : ∀ y ∈ s, G.Adj y (l.getD p x₀)) (hsq : ∀ y ∈ s, G.Adj y (l.getD q x₀))
    (hσ : secondSmallestDegree G ≤ s.length + 1) (hg : q - p - 1 ≤ s.length) : False
```
**Usage** (avec miroir B1 pour x₀ = x_{q−1}) : D⁺ σ=4 (p,q)=(4,7) ; cas B σ=4 (4,7), (5,8), (4,8) avec x₀ = x_{p+1}
ou x_{q−1} ; K₄ σ=5 (5,8). Remplace 5 cas « à la main » de M2.2/M2.7 (et leurs miroirs). **Taille** 220.

### B20 — Degré d'une extrémité (outil des cas (C))
```lean
lemma Cadre.head_deg_le (hC) (C : Finset ℕ)
    (hex : ∀ j, 0 < j → j < l.length → j ∉ C → ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀)) :
    G.degree (l.getD 0 x₀) ≤ C.card
lemma Cadre.head_forced (hC) (C : Finset ℕ) (hex : …) (hdeg : C.card ≤ G.degree (l.getD 0 x₀)) :
    ∀ j ∈ C, G.Adj (l.getD 0 x₀) (l.getD j x₀)
lemma Cadre.last_deg_le … / Cadre.last_forced …   -- par hC.reverse
```
**Preuve.** N(x₁) ⊆ P (`lemma4x`) ⇒ N(x₁) ⊆ image de C. head_forced : sinon C.erase j convient.
**Recettes d'exclusion** (une ligne chacune, à fournir pour `hex` après `interval_cases j`) :
- (L4) x₁ ≁ x_m : 4e composante de `lemma4x` avec j = m−2 et l'arête x_{m−1}x_m.
- (5b) y ∈ R, y ~ x_a ⇒ x₁ ≁ x_{a+1} ; et x_m ≁ x_{a−1} (`lemma5abx`).
- (Γ) Γ(u) « exact » : si S ⊆ L₂(u), |S| = σ, x_j ∉ S, u ~ x_a, x_j ~ x_a, u ≁ x_j ⇒ ✗ (B3 sur insert x_j S).
- (E) B6 / B6-miroir.
- (X) croisement : x₁ ~ x_{j+1} ⇒ x_j ≁ x_m (4e composante de `lemma4x`).
**Taille** 140.

---

## 4. R = K₃ : Théorème D⁺ (m = 2σ+2) et D⁺⁺ cas B (m = 2σ+3) (Lot 4)

### B21 — Lemme K₃ (partie générique)
```lean
lemma Cadre.K3 (hC) (u v w : V) (hR : Rset l = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hm : l.length = 2 * secondSmallestDegree G + 2 ∨ l.length = 2 * secondSmallestDegree G + 3) : False
```
**Preuve.**
1. σ = 2 : B15 ⇒ m ≥ 8 > 2σ+3. ✗ Désormais σ ≥ 3.
2. y ∈ R : k(y) = 2, c(y) = deg y − 2 ≥ σ − 2 ≥ 1 (B8). B9 avec B'_y = {x_a : a ∈ A, y ≁ x_a} (porteur ∈ R\{y},
   voisin de y), K₂ = ∅ : c + 1 + |B'_y| ≤ σ ⇒ **|B'_y| ≤ 1** et c(y) ≤ σ − 1.
3. **Tout écart consécutif est croisé** : sinon un seul porteur y des deux attaches, et v ∈ R \ {y} les manque toutes
   les deux : |B'_v| ≥ 2. ✗
4. Régions (B5 avec les chemins hamiltoniens de K₃, 3 sommets, entre deux sommets distincts quelconques) :
   gauche ≥ 3 ou contient x₀ ; droite idem ; écart consécutif : ≥ 1 toujours, ≥ 3 ou contient x₀.
5. B16 (k = 3, E = ∅) : **m ≥ 4r + 1**, avec r ≥ c(u) ≥ σ − 2 et r ≥ 2 (B13).
6. Répartition (omega) :
   - m = 2σ+2 : σ = 3 donne 8 ≥ 9 ✗ ; σ ≥ 5 donne 2σ+2 ≥ 4σ−7 ✗ ; **σ = 4, m = 10, r = 2**.
   - m = 2σ+3 : σ ≥ 6 ✗ ; **σ = 3, m = 9, r = 2** ; **σ = 4, m = 11, r = 2** ; **σ = 5, m = 13, r = 3**.
   - σ = 4, 5 : c(y) ≥ σ − 2 = r ⇒ **chaque y voit tout A** (J(y) = A).
7. r = 2 : A = {p < q} (`Finset.card_eq_two`) ; r = 3 : `card_eq_three`. Les faits de régions + 0 < i₀ < m−1 +
   `omega`/`interval_cases` donnent exactement la table 4.1 ; chaque ligne renvoie à B17, B18, B19 ou à un cas B22,
   les lignes « miroir » passent par `hC.reverse` (A ↦ m−1−A, i₀ ↦ m−1−i₀).
**Dépend** : B5, B8, B9, B13, B15–B19, B22. **Taille** 350.

### 4.1 Table des sous-cas K₃ (indices maths 1-indexés ; P, Q = attaches ; L, M, Rr = tailles des régions)
| m (σ) | configuration | issue |
|---|---|---|
| 10 (σ=4, D⁺) | Q = P+2 | M = 1 contient x₀ = x_{P+1} ; **B17** : 3+2 ≤ 4 ✗ |
| 10 | x₀ ∈ A | L, M, Rr ≥ 3 : 9 > 8 ✗ (omega) |
| 10 | x₀ à gauche | L = 2, M = Rr = 3 : (P,Q) = (3,7), x₀ = x₂ : **C1** |
| 10 | x₀ à droite | miroir de C1 |
| 10 | x₀ au milieu, M = 2 | (P,Q) = (4,7), x₀ = x₅ : **B19** (|s| = 3, g = 2) ; x₀ = x₆ : miroir B19 |
| 9 (σ=3, cas B) | x₀ ∈ A / à gauche / à droite | ≥ 9 / ≥ 8 / ≥ 8 > 7 ✗ (omega) |
| 9 | x₀ au milieu | L = Rr = 3 ⇒ M = 1, x₀ = x_{P+1} ; **B17** (S = R, chacun voit x_P ou x_Q) : 5 ≤ 3 ✗ |
| 11 (σ=4, cas B) | Q = P+2 | **B17** : 5 ≤ 4 ✗ |
| 11 | x₀ ∈ A | **B18** : 5 ≤ 4 ✗ |
| 11 | x₀ à gauche, L = 2 | (3,7) : **C3** ; (3,8) : **C4** (x₀ = x₂) |
| 11 | x₀ à gauche, L = 3 | (4,8), x₀ ∈ {x₂, x₃} : **C5** |
| 11 | x₀ à droite | miroirs de C3, C4, C5 |
| 11 | x₀ au milieu, M = 2 | (4,7) ou (5,8), x₀ = x_{P+1} : **B19** ; x₀ = x_{Q−1} : miroir B19 |
| 11 | x₀ au milieu, M = 3 | (4,8) : x₀ = x₅ **B19** (g = 3 ≤ 3), x₀ = x₇ miroir, **x₀ = x₆ : C9** |
| 13 (σ=5, cas B) | x₀ ∈ A / extrémité | ≥ 15 / ≥ 14 > 13 ✗ (omega) |
| 13 | x₀ dans un écart | serré : régions (3,1,3,3) [A = {4,6,10}, x₀ = x₅] ou (3,3,1,3) [A = {4,8,10}, x₀ = x₉] : **C10** + miroir |

### B22 — Cas concrets K₃ (comptage (C) de B20)
Hypothèses communes (Lean, 0-indexé) : `hC`, σ et `l.length` numéraux, R = {u,v,w} clique, **tous voient A**,
position de x₀. Forme : `lemma Cadre.C1 (hC) (hσ : secondSmallestDegree G = 4) (hm : l.length = 10) (u v w …)
(hA : ∀ y ∈ ({u,v,w} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 6 x₀)) (hx : l.getD 1 x₀ = x₀) : False`.
Dans chaque cas : S(u) = x(D(u)) ⊆ L₂(u) avec |S| = σ (« Γ(u) exact »), exclusions (5b), (L4), (Γ), (E) de B20,
puis `head_deg_le` (ou `last_deg_le`) avec la liste C des candidats restants. (E) : chemin K, x_a, …, x₁, x_j, …, x_m
de |K| + a + m − j + 1 sommets (maths), à garder s'il contient x₀.

| cas | m, σ | A (maths) | x₀ | S(u) | exclusions de N(x₁) | candidats restants | conclusion |
|---|---|---|---|---|---|---|---|
| **C1** | 10, 4 | {3,7} | x₂ | x₂,x₄,x₆,x₈ | 5b x₄,x₈ ; L4 x₁₀ ; Γ x₃,x₇ ; E j ≤ 6 : x₅,x₆ | {x₂, x₉} | deg x₁ ≤ 2 < 4 ✗ |
| **C3** | 11, 4 | {3,7} | x₂ | x₂,x₄,x₆,x₈ | 5b x₄,x₈ ; L4 x₁₁ ; Γ x₃,x₇ ; E j ≤ 6 | {x₂, x₉, x₁₀} | 3 < 4 ✗ |
| **C4** | 11, 4 | {3,8} | x₂ | x₂,x₄,x₇,x₉ | 5b x₄,x₉ ; L4 x₁₁ ; Γ x₃,x₈ ; E j ≤ 6 | {x₂, x₇, x₁₀} | 3 < 4 ✗ |
| **C5** | 11, 4 | {4,8} | x₂ ou x₃ | x₃,x₅,x₇,x₉ | 5b x₅,x₉ ; L4 x₁₁ ; Γ x₄,x₈ ; E (a=4) j ≤ 7 | {x₂, x₃, x₁₀} | 3 < 4 ✗ |
| **C9** | 11, 4 | {4,8} | x₆ | x₃,x₅,x₇,x₉ | x₁ : 5b x₅,x₉ ; L4 ; Γ x₄,x₈ ; E j ∈ {5,6} (x₀ ∈ chemin ⇔ j ≤ 6) | N(x₁) = {x₂,x₃,x₇,x₁₀} **forcé** | voir ci-dessous |
| **C10** | 13, 5 | {4,8,10} | x₉ | x₃,x₅,x₇,x₉,x₁₁ | 5b x₅,x₉,x₁₁ ; L4 x₁₃ ; Γ x₄,x₈,x₁₀ ; E (a=4) j ≤ 7 | {x₂, x₃, x₁₂} | 3 < 5 ✗ |

C9 (suite) : x₁₁ : 5b x₃, x₇ ; L4 x₁ ; Γ x₄, x₈ ; E-miroir (a_r = 8 : chemin x₁…x_j x₁₁ x₁₀ x₉ x₈ K, j + 7 sommets,
contient x₀ ⇔ j ≥ 6) : x₆, x₇. Restent {x₂, x₅, x₉, x₁₀} = 4 = σ : **forcé** x₁₁ ~ x₂. Or x₁ ~ x₃ : croisement (X) ✗.
Indices Lean (= maths − 1) : C1 A = {2,6}, i₀ = 1, C = {1,8} ; C3 A = {2,6}, C = {1,8,9} ; C4 A = {2,7}, C = {1,6,9} ;
C5 A = {3,7}, i₀ ∈ {1,2}, C = {1,2,9} ; C9 A = {3,7}, i₀ = 5, C_tête = {1,2,6,9}, C_queue = {1,4,8,9} ;
C10 A = {3,7,9}, i₀ = 8, C = {1,2,11}. (B6 : condition Lean `j − a ≤ s.length`.)
**Écart avec research-189 (signalé, pas une erreur de conclusion).** M2.7 cas B σ=5 « (C) force N(x₁₃) =
{x₂,x₇,x₈,x₁₁,x₁₂} » n'applique (E) qu'en a₁ ; avec (E) en a_r, x₇, x₈ sont exclus et deg x₁₃ ≤ 3 : on garde cette
version courte (C10 = forme « tête » du miroir). Les autres cas de M2.2/M2.7 ont été recalculés : identiques.
**Taille** : 6 cas × 70 ≈ 420.

---

## 5. |R| = 4, m = 2σ+2 : D⁺⁺ cas A, puis assemblage (Lot 5)

### B23 — R non-clique (C₄ et diamant, preuve unifiée — réparation verif-D intégrée)
```lean
lemma Cadre.R4_nonclique (hC) (z z' a b : V) (hR : Rset l = {z, z', a, b}) (hd : [6 distinctions])
    (hzz : ¬ G.Adj z z') (h1 : G.Adj z a) (h2 : G.Adj z b) (h3 : G.Adj z' a) (h4 : G.Adj z' b)
    (hm : l.length = 2 * secondSmallestDegree G + 2) : False
```
**Preuve.** σ ≤ 3 : B15 (m ≥ 9 > 8). ✗ Soit σ ≥ 4.
(α) ζ ∈ {z, z'} : k(ζ) = 2, c(ζ) ≥ σ − 2 ≥ 2, K₂(ζ) ∋ ζ' (via a). B9 avec B'_ζ = {x ∈ P : x ≁ ζ, x ~ a ∨ x ~ b} et
K₂ = {ζ'} : (2c − t) + |B'_ζ| + 1 ≤ σ ≤ c + 2 et 2c − t ≥ c + 1 ⇒ **B'_ζ = ∅, t(ζ) = c(ζ) − 1, c(ζ) = σ − 2**.
Donc J(a) ∪ J(b) ⊆ J(z) ∩ J(z') et J(ζ) est une progression de pas 2 (B7 `prog`).
(β) **Privauté** : j ∈ T(ζ), x_{j+1} ≠ x₀ ⇒ aucun w ∈ R \ {ζ} ne voit x_j ni x_{j+2}. Sinon `no_mid` remplace x_{j+1}
par un chemin w → ζ de ≥ 2 sommets : [a,ζ], [b,ζ], [ζ',a,ζ] (et renversés côté x_{j+2}). (Pas besoin de chemin
hamiltonien : en C₄, z' → z n'en a pas, mais [z',a,z] suffit.)
(γ) σ ≥ 5 : c(a) ≥ σ − 3 ≥ 2 ; j₁ < j₂ dans J(a) ⊆ J(z). j₁ ≠ max J(z) ⇒ j₁ ∈ T(z) ⇒ (β) x_{j₁+1} = x₀. Si j₂ ≠ max,
idem x_{j₂+1} = x₀ ✗ (Nodup) ; donc j₂ = max ≠ min, j₂ − 2 ∈ T(z), (β) ⇒ x_{j₂−1} = x₀ ⇒ j₂ = j₁ + 2. Si j₁ ≠ min J(z),
j₁ − 2 ∈ T(z) ⇒ x_{j₁−1} = x₀ ✗. Donc J(z) ⊆ [j₁, j₁+2], et j₁+1 ∉ J(z) (5a) ⇒ c(z) = 2 < 3. ✗
(δ) σ = 4 : c(z) = 2, J(z) = {p, p+2}. c(a) ≥ 1 et J(a) ⊆ {p,p+2} ⇒ (β) x_{p+1} = x₀. De même J(z') = {p', p'+2},
x_{p'+1} = x₀ ⇒ p' = p ; donc A = {p, p+2}. Gauche (sans x₀) : `no_pre` avec [b,z',a,z] ⇒ p − 1 ≥ 4 ;
droite : `no_suf` avec [z,a,z',b] ⇒ m − p − 2 ≥ 4. m ≥ 11 > 10. ✗
**Dépend** : B5, B7, B8, B9, B15. **Taille** 300.

### B24 — R = K₄
```lean
lemma Cadre.R4_clique (hC) (a b c d : V) (hR : Rset l = {a, b, c, d}) (hd : [6 distinctions]) (hadj : [6 adjacences])
    (hm : l.length = 2 * secondSmallestDegree G + 2) : False
```
**Preuve.** σ ≤ 3 : B15. ✗ σ ≥ 4 : c(y) = deg y − 3 ≥ σ − 3 ≥ 1 ; B9 (B'_y = A \ N_P(y), K₂ = ∅) ⇒ **|B'_y| ≤ 2**.
E := attaches qui ouvrent un écart consécutif **non croisé** (seul porteur y). **|E| ≤ 1** : deux tels écarts
(a,b), (a',b'), a < a' ⇒ a < b ≤ a' < b' ; un w ∈ R \ {y, y'} manque a, a', b' : |B'_w| ≥ 3. ✗
Régions : écarts croisés ≥ 4 (chemin hamiltonien de K₄ entre porteurs distincts) sauf x₀ ; extrémités ≥ 4 sauf x₀.
B16 (k = 4) : **m ≥ 5r − 2**, r ≥ σ − 3, r ≥ 2.
- σ ≥ 7 : 2σ+2 ≥ 5σ − 17 ✗.
- σ = 6 (m = 14) : r = 3, c ≥ 3 = r ⇒ tous voient A ⇒ E = ∅ ⇒ m ≥ 5r + 1 = 16 ✗.
- σ = 4 (m = 10) : r = 2 ; l'écart est **croisé** (sinon les trois autres ont c = 0 < 1 = σ − 3 : trou mineur de
  verif-D comblé) ; régions ≥ 4, 4 et ≥ 1 : 9 > 8 ✗ (x₀ ∈ A : 12 > 8).
- σ = 5 (m = 12) : r = 2, c ≥ 2 = r ⇒ tous voient A = {P,Q}. Table :

| configuration | issue |
|---|---|
| Q = P+2 | **B17** : 4+2 ≤ 5 ✗ |
| x₀ ∈ A | **B18** : 6 ≤ 5 ✗ |
| x₀ à gauche | L = 2, M = Rr = 4 : (3,8), x₀ = x₂ : **C11** |
| x₀ à droite | miroir C11 |
| x₀ au milieu | L = Rr = 4, M = 2 : (5,8), x₀ = x₆ **B19** (|s| = 4, g = 2) ; x₀ = x₇ miroir |

**C11** (m = 12, σ = 5, A = {3,8}, x₀ = x₂ ; Lean A = {2,7}, i₀ = 1). x₁ : 5b x₄, x₉ ; L4 x₁₂ ; E (a = 3, |K| = 4 :
20 − j > 12 ⇔ j ≤ 7) x₄…x₇ ⇒ candidats {x₂,x₃,x₈,x₁₀,x₁₁} = 5 = σ : **forcé** x₁ ~ x₃ (Lean C = {1,2,7,9,10}).
Alors S' = {x₁,x₂,x₄,x₇,x₉} ⊆ L₂(u), |S'| = 5 = σ. x₁₂ : 5b x₂, x₇ ; L4 x₁ ; Γ(S') x₃, x₈ ; E-miroir (a_r = 8 :
j + 9 > 12 ⇔ j ≥ 4, x₀ = x₂ dedans) x₄…x₇ ⇒ candidats {x₉,x₁₀,x₁₁} : 3 < 5 ✗ (Lean C_queue = {8,9,10}).
**Dépend** : B5, B9, B15–B20. **Taille** 350 + 80 (C11).

### B25 — Assemblage D / D⁺ / D⁺⁺
```lean
theorem thm_D_all {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn1 : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V)
    (hn2 : Fintype.card V ≤ 2 * secondSmallestDegree G + 6) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian
```
**Preuve.** B1(c) : hamiltonien ou cadre. B12 : m ≥ 2σ+2 ; B14 : |R| = n − m ∈ {3, 4}.
|R| = 3 : `Cadre.R3` puis B21 (m = n − 3 ∈ {2σ+2, 2σ+3}). |R| = 4 : m = 2σ+2, `Cadre.R4` puis B23 / B24. **Taille** 120.

### B26 — Fichier de réduction R2.H2.R1
```lean
def H1 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj],
  G.Connected → (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
  2 * secondSmallestDegree G + 7 ≤ Fintype.card V → (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
  G.minDegree = secondSmallestDegree G → ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian
def H2 : Prop := … (même chose avec `G.minDegree < secondSmallestDegree G`)
theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.H2
```
**Preuve.** n ≤ 2σ+6 : B25. Sinon minDegree ≤ σ (B2 avec x₀ = sommet de degré minimum, `minDegree_le_degree` /
`exists_minimal_degree_vertex`) ; `lt_or_eq` ⇒ H2 ou H1. **Taille** 60.

---

## 6. Découpage en lots parallélisables

Règle : un fichier d'interfaces commun `Interfaces.lean` (structure `Cadre`, définitions `Jset/Dset/Tset/Rset`, et
**toutes les signatures ci-dessus avec `sorry`**) est figé d'abord ; chaque lot remplit ses corps contre ces
signatures ; la fusion finale concatène dans l'ordre B1 → B26 (fichier unique de réduction).

| Lot | Contenu | Interfaces fournies | Interfaces consommées | Taille |
|---|---|---|---|---|
| **1 Socle** | B1–B6 : Cadre, copies H1, miroir, deg x₀ ≤ σ, Γ, coupure, chirurgie, (E) | `Cadre.*`, `cut_closed`, `card_le_gamma`, `deg_x0_le`, `no_*`, `endE` | — | ≈ 570 + 550 copiées |
| **2 Comptage/structure** | B7–B14 : anneau, (Q2) corrigé, E′, (Q3) global, (R4), (R6), forme de R, Théorème D | `ring_card`, `prog`, `count_Q2`, `Rdeg2`, `m_ge`, `two_attach`, `R3`, `R4` | Lot 1 ; B17 (dans E′) | ≈ 1 230 |
| **3 Régions/x₀ local** | B15–B20 : petits σ, `pack` (pur), trou-x₀, x₀-attache, marche-x₀, degré d'extrémité | `small_sigma`, `pack`, `hole_x0`, `x0_attach`, `walk_x0`, `head_deg_le` | Lot 1 ; B8/B13 | ≈ 860 |
| **4 K₃** | B21–B22 : D⁺ et D⁺⁺ cas B, cas C1, C3, C4, C5, C9, C10 | `Cadre.K3` | Lots 1–3 | ≈ 770 |
| **5 |R| = 4 + final** | B23–B26 : non-clique, K₄ (+ C11), assemblage, `main` | `thm_D_all`, `main` | Lots 1–4 | ≈ 910 |

Total estimé **≈ 4 900 lignes** (≈ 4 350 neuves + ≈ 550 copiées), fourchette 4 000–5 500.
Indépendants de tout : B7 et B16 (purs ℕ), à confier en premier à un exécutant Haiku/Sonnet.

## 7. Points délicats
1. **E1 intégré** : B'_y = N_P(N_R(y)) \ N_P(y) partout (B9) ; la disjonction D/B' n'utilise qu'une insertion de
   [y,z]. C₄ et diamant sont traités ensemble (B23), via la privauté (β) qui n'exige qu'un chemin w → ζ de ≥ 2 sommets.
2. **Trou mineur K₄ σ = 4** (verif-D) : comblé (écart croisé car c ≥ 1 pour tous).
3. **Plus de dépendance aux balayages numériques** (research H2.4 invoquait n ≤ 11 pour σ ≤ 3) : σ ≤ 3 est réglé par
   B15/B16. (Q4) « K₃ ⇒ σ ≤ 5 » est remplacé par m ≥ 4r + 1 (B16).
4. Coûts Lean dominants : B12 (adaptation de `caseA`), B5/B19 (concaténations take/drop/reverse : prévoir des
   lemmes `getD_take/drop/reverse`), B16 (récurrence), et l'énumération omega des positions dans B21/B24
   (`Finset.card_eq_two/three`, `interval_cases` sur p, q, i₀ bornés par m numéral).
5. Aucun pas de preuve jugé faux en dehors des erreurs déjà relevées par verif-D ; seul écart de rédaction :
   M2.7 cas B σ=5 (exclusions de x₁₃ incomplètes, conclusion juste) — remplacé par C10.

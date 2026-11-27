# WOWII 189 — journal de recherche (preuve partielle + réduction)

Énoncé (Lean, `GraphConjecture189.lean`) : G simple, connexe, n = |V| ≥ 2 ; si max_v distEven(v) ≤ 1 + σ(G), alors G a un chemin hamiltonien.
`distEven(v)` = #{w : d(v,w) pair} (v compris) ; σ = `secondSmallestDegree` = d₂ de la suite des degrés triée (doublons compris).

## 0. Notations
- E(v) = distEven(v) ; Γ(v) = {w ≠ v : d(v,w) pair}, donc E(v) = 1 + |Γ(v)| ; O(v) = n − E(v) ; L_k(v) = sphère de rayon k.
- F(v) = {w : d(v,w) impair et ≥ 3}. Partition : V = {v} ⊔ N(v) ⊔ Γ(v) ⊔ F(v), donc |F(v)| = n − 1 − deg v − |Γ(v)|.
- (H) : |Γ(v)| ≤ σ pour tout v.
- x₀ : un sommet fixé de degré minimum δ. **Fait 0** : tout v ≠ x₀ vérifie deg v ≥ σ (les degrés des autres sommets forment le multiensemble {d₂,…,d_n}).
- Si n ≥ 3, G connexe ⇒ tous les degrés ≥ 1, donc σ ≥ 1.
- Chemin le plus long P = x₁…x_m ; R = V \ V(P). I₁ = {i ∈ [1,m−1] : x₁ ~ x_{i+1}}, I_m = {i ∈ [1,m−1] : x_m ~ x_i} ; |I₁| = deg x₁, |I_m| = deg x_m (si N(x₁), N(x_m) ⊆ V(P)).

## 1. Tests (C + nauty-geng, scripts dans `wowii/r189/`)
- Hypothèse vérifiée par : n=5:15, 6:51, 7:247, 8:1476, 9:22 575, 10:418 415 graphes connexes. Aucun non traçable (cohérent avec le balayage n ≤ 11 de `search.md`).
- Diamètre ≥ 3 sous (H) : 1/3/19/78/446/5612 (n=4..9) ; non bipartis presque tous. Ore « chemins » (deg u + deg v ≥ n−1 pour u≁v) échoue **exactement** sur les graphes de diamètre ≥ 3 ⇒ aucune approche « Ore global ».
- Fermeture de Bondy–Chvátal (seuil n−1) non complète seulement pour C₆, C₇, Q₃ et un 3-régulier à 8 sommets (n ≤ 9). Condition de Chvátal (chemins) et Chvátal–Erdős (α ≤ κ+1) échouent sur des graphes de (H) (κ=1 surtout) ⇒ pas de réduction directe à ces théorèmes.
- 2-connexes sous (H) non hamiltoniens : seulement n impair (n=5:2, 7:6, 9:19), du type « indépendant de taille (n+1)/2 ».
- Aucun sommet d'articulation laissant ≥ 3 composantes (n ≤ 9) — prouvé ci-dessous (Lemme 6).
- **Histogramme n − 2σ** sous (H) : n ≤ 6 : ≤ 2 ; n=7 : 3 (5 graphes, dont C₇) ; n=8 : ≤ 2 ; n=9 : 3 (100 graphes) ; n=10 : 4 (29 graphes, σ=3, ex. `I?aJbdrbw`, κ=1, n = 3σ+1). Résultat n=11 : 7 186 (tous n = 2σ+3).
- Le témoin d'un graphe non traçable n'est PAS toujours hors du plus long chemin (14 échecs à n=9, ex. `HCOceQd` : triangle central + 3 triangles pendants, témoin = sommet d'articulation).
- Éclatés de C₇ (chaque sommet → clique K_t, cliques voisines jointes) : (H) vraie, n = 7t, σ = 3t−1, n − 2σ = t+2 **non borné** (vérifié t=1..4 ; aussi tailles inégales [3,2,3,2,3,2,2]). Hamiltoniens.

## 2. Lemmes

**Lemme 1 (identité d'arête).** Pour u ~ v, soit S = {w : d(u,w)=d(v,w)}, S_p/S_i ses parties paire/impaire. Alors E(u)+E(v) = n − |S_i| + |S_p|.
*Preuve.* |d(u,w) − d(v,w)| ≤ 1. Si w ∉ S, les distances diffèrent de 1, exactement une est paire (contribue 1) ; si w ∈ S, contribue 2 (pair) ou 0 (impair). □
*Corollaire 1a.* Si une arête uv a |S_i| ≤ |S_p| (en particulier S = ∅ : pont, feuille, toute arête d'un graphe biparti), (H) ⇒ n ≤ 2σ + 2.
*Corollaire 1b.* Si δ = 1 (x₀ feuille de voisin c) : E(x₀)+E(c) = n, donc (H) ⇒ n ≤ 2σ+2.

**Lemme 2 (excentricité ≤ 2).** Si ecc(v) ≤ 2, E(v) = n − deg v ; donc (H) ⇒ deg v ≥ n − 1 − σ, i.e. n ≤ σ + 1 + deg v.
*Corollaire 2a.* Si diam G ≤ 2 : prendre u ≠ x₀ avec deg u = σ (existe : d₂ est atteint par un sommet ≠ x₀) ⇒ n ≤ 2σ + 1.

**Lemme 3 (sommets à distance impaire ≥ 3).** Si w ∈ F(v) alors N(w) ∩ N[v] = ∅, donc N(w) ⊆ (V \ N[v]) \ {w}. De plus (H) ⇒ |F(v)| ≥ |V \ N[v]| − σ. □

**Lemme 4 (cycle d'Ore sur un plus long chemin).** P plus long, m < n, G connexe ⇒ N(x₁),N(x_m) ⊆ V(P), x₁ ≁ x_m, I₁ ∩ I_m = ∅, donc deg x₁ + deg x_m ≤ m − 1.
*Preuve.* Si i ∈ I₁ ∩ I_m, C = x₁x₂…x_i x_m x_{m−1}…x_{i+1}x₁ est un cycle sur V(P) ; comme m < n et G connexe, un y ∉ V(P) est adjacent à un sommet de C ; on ouvre C en ce sommet : chemin à m+1 sommets. Contradiction. □

**Lemme 5 (sommet hors du chemin).** P plus long, y ∈ R, y ~ x_j. Alors (a) 2 ≤ j ≤ m−1, y ≁ x_{j±1} ; (b) x₁ ≁ x_{j+1} (sinon y x_j x_{j−1}…x₁ x_{j+1}…x_m) et x_m ≁ x_{j−1} (sinon x₁…x_{j−1} x_m…x_j y) ; i.e. j ∉ I₁ et j−1 ∉ I_m.
(c) [**Lemme L2**] Si de plus N(y) ⊆ V(P) et deg y = k ≥ 1, alors |Γ(y)| ≥ k + 1 ; donc sous (H), y = x₀ et deg x₀ ≤ σ − 1.
*Preuve de (c).* N(y) = {x_{j₁},…,x_{j_k}}, j₁<…<j_k. Les k+1 sommets x_{j₁−1}, x_{j₁+1},…,x_{j_k+1} sont distincts (indices distincts), non adjacents à y (a), adjacents à un voisin de y : distance exactement 2. Si y ≠ x₀, deg y ≥ σ (Fait 0) ⇒ |Γ(y)| ≥ σ+1, contredit (H). □

**Lemme 6 (sommet d'articulation).** Soit c d'articulation, C₁, C₂ deux composantes de G − c, u_i ∈ C_i ∩ N(c).
(a) |Γ(u₁)| + |Γ(u₂)| + |Γ(c)| ≥ n − 1 ; donc (H) ⇒ **n ≤ 3σ + 1**.
(b) (H) ⇒ G − c a **exactement deux** composantes.
*Preuve.* (a) Pour w ∉ C₁ ∪ {c}, tout chemin u₁–w passe par c : d(u₁,w) = 1 + d(c,w) ; idem u₂. Un w ≠ c à distance paire de c est dans Γ(c) ; à distance impaire, il est dans Γ(u₂) s'il est hors de C₂, dans Γ(u₁) s'il est hors de C₁. Chaque w ≠ c est compté au moins une fois. (b) Toute composante D ≠ {x₀} contient z ≠ x₀, deg z ≥ σ, N(z) ⊆ D ∪ {c} ⇒ |D| ≥ σ. Trois composantes « grosses » : la somme de (a) compte en plus les w de C₃ à distance impaire de c (≥ |N(c) ∩ C₃| ≥ 1) : 3σ ≥ n − 1 + 1 ≥ 3σ + 1, absurde. Si une composante est {x₀} : δ = 1, Cor. 1b ⇒ n ≤ 2σ+2, or n ≥ 2 + |C₂| + |C₃| ≥ 2σ+2 ⇒ exactement 3 composantes, |C₂| = |C₃| = σ, chaque C_i ∪ {c} est une clique (degré ≥ σ dans un ensemble de σ+1 sommets) ⇒ Γ(x₀) = C₂ ∪ C₃, |Γ(x₀)| = 2σ > σ. Absurde. □

## 3. Théorème C (preuve complète)
**Théorème C.** G connexe, n ≥ 2, (H) et **n ≤ 2σ + 2** ⇒ G traçable.

*Preuve.* n = 2 : K₂. Soit n ≥ 3 (σ ≥ 1) et supposons G non traçable ; m < n est le nombre de sommets d'un plus long chemin ; m ≥ 3 (G connexe, n ≥ 3, contient P₃).

**Cas A : il existe un plus long chemin P = x₁…x_m avec x₁, x_m ≠ x₀.**
A1. Fait 0 + Lemme 4 : 2σ ≤ deg x₁ + deg x_m ≤ m − 1 ≤ n − 2 ≤ 2σ. Donc m = n−1 = 2σ+1, n = 2σ+2, deg x₁ = deg x_m = σ, I₁ ⊔ I_m = [1, m−1] (partition), R = {y}.
A2. N(y) ⊆ V(P), deg y ≥ 1 ⇒ y = x₀ (Lemme 5c).
A3. Pour tout x_j ∈ N(y) : j ∉ I₁ ⇒ j ∈ I_m ⇒ x_m ~ x_j ; j−1 ∉ I_m ⇒ j−1 ∈ I₁ ⇒ **x₁ ~ x_j** (Lemme 5b + partition). Donc d(x₁,y) = 2 et N(y) ⊆ N(x₁).
A4. V \ N[x₁] = {y} ∪ N(x_m)⁺ où N(x_m)⁺ = {x_{i+1} : i ∈ I_m} : pour 2 ≤ k ≤ m, x_k ∉ N(x₁) ⇔ k−1 ∉ I₁ ⇔ k−1 ∈ I_m. Taille σ + 1.
A5. |Γ(x₁)| ≤ σ < σ+1 ⇒ il existe w ∈ V \ N[x₁] avec d(x₁,w) impaire ≥ 3 (Lemme 3) ; w ≠ y (A3), donc w ∈ N(x_m)⁺.
A6. N(w) ⊆ (V \ N[x₁]) \ {w} (Lemme 3) ; y ∉ N(w) car N(y) ⊆ N(x₁) ∌ w. Donc N(w) ⊆ N(x_m)⁺ \ {w} : deg w ≤ σ − 1. Or w ≠ y = x₀ ⇒ deg w ≥ σ. Contradiction.

**Cas B : tout plus long chemin a x₀ pour extrémité.** Si deg x₀ ≥ 2 : P = x₀x₂…x_m, x₀ a un voisin x_j, j ≥ 3 (Lemme 4 : N(x₀) ⊆ V(P)) ; la rotation x_{j−1}…x₂ x₀ x_j…x_m est un plus long chemin d'extrémités ≠ x₀ : Cas A. Donc δ = 1 ; soit c l'unique voisin de x₀, P = x₀ c x₃…x_m, G* = G − x₀ (connexe).
B1. P* = c x₃…x_m est un plus long chemin de G* (un chemin de G* à ≥ m sommets serait un plus long chemin de G sans x₀).
B2. N_{G*}(c) ⊆ V(P*) : si c ~ y ∈ R, y c x₃…x_m est un plus long chemin de G sans x₀. Et N(x_m) ⊆ V(P) \ {x₀} (x_m ≠ c).
B3. Lemme 4 dans G* (m−1 < n−1) : (deg c − 1) + deg x_m ≤ m − 2, avec deg c, deg x_m ≥ σ ⇒ m ≥ 2σ+1. Avec m ≤ n − 1 ≤ 2σ+1 : R = {y}, y ≠ x₀, N(y) ⊆ V(P) ⇒ |Γ(y)| ≥ σ+1 (Lemme 5c). Contradiction. □

### Corollaires (la conjecture 189 est vraie si) :
- diam G ≤ 2 (Cor. 2a) ; plus généralement s'il existe v d'excentricité ≤ 2 avec deg v ≤ σ+1 (Lemme 2) ;
- G biparti, ou G a un pont, ou δ = 1, ou une arête avec |S_i| ≤ |S_p| (Cor. 1a/1b) ;
- empiriquement : tous les graphes de (H) avec n pair ≤ 8, et n ≤ 6 ; à n=9, 22 475/22 575 ; à n=10, 418 386/418 415 ; à n=11, 27 422 036/27 429 222.

## 4. Réduction : cas ouvert restant
**Il reste exactement : (H) et n ≥ 2σ + 3.** Propriétés prouvées dans ce régime (pour un éventuel contre-exemple minimal ou non) :
- (R1) δ ≥ 2, σ ≥ 2 (σ = 1 ⇒ δ = 1), pas de pont, non biparti ; chaque arête uv a |S_i(u,v)| ≥ |S_p(u,v)| + n − 2σ − 2 ≥ |S_p| + 1 (Lemme 1).
- (R2) tout sommet de degré ≤ n − 2 − σ (en particulier de degré ≤ σ+1) a une excentricité ≥ 3 (Lemme 2).
- (R3) si G a un sommet d'articulation : exactement 2 composantes et n ≤ 3σ + 1 (Lemme 6).
- (R4) si G est non traçable : tout plus long chemin d'extrémités ≠ x₀ (il en existe, δ ≥ 2) vérifie m ≥ max(2σ+2, deg x₁ + deg x_m + 1). Preuve du cas m = 2σ+1 exclu (généralise A) : partition I₁ ⊔ I_m, tout sommet de R ayant un voisin sur P est à distance 2 de x₁ (A3) ; un w ∈ F(x₁) ∩ V(P) a N(w) ⊆ N(x_m)⁺ \ {w} donc w = x₀ ; un w ∈ F(x₁) ∩ R n'a aucun voisin sur P (ensemble R₀ ⊊ R). |F(x₁)| ≥ σ + |R| − σ = |R| et F(x₁) ⊆ {x₀} ∪ R₀ ⇒ x₀ ∈ V(P), |R₀| = |R| − 1, un seul y₁ ∈ R a des voisins sur P. Si |R| = 1 : Lemme 5c. Sinon y₁ est d'articulation, z ∈ R₀ a deg ≥ σ et N(z) ⊆ R ⇒ |R| ≥ σ+1 ⇒ n ≥ 3σ+2, contredit Lemme 6a. □
- (R5) dans ce régime, les singletons de G[R] sont ⊆ {x₀} (Lemme 5c) ; les composantes non triviales de G[R] restent le trou principal.
- (R6) G non traçable, P comme en (R4) : **toute composante H de G − V(P) a ≥ 2 sommets d'attache sur P.** Preuve : si N_P(H) = {x_i}, x_i est d'articulation (sépare H de V(P) \ {x_i}) ⇒ n ≤ 3σ+1 (Lemme 6a). H ≠ {x₀} (δ ≥ 2) et un singleton ≠ x₀ est exclu (Lemme 5c), donc H contient z ≠ x₀ avec N(z) ⊆ (H \ {z}) ∪ {x_i} ⇒ |H| ≥ σ ⇒ n ≥ m + |H| ≥ 2σ+2+σ = 3σ+2. Contradiction. □
- Le régime est infini et non « presque Dirac » : éclatés de C₇ avec n − 2σ = t + 2 → ∞ (tous hamiltoniens). Donc toute preuve du cas restant doit exploiter une structure de type cycle impair (C₇) et non une borne n ≤ 2σ + O(1).
- Données : graphes de (H) avec n ≥ 2σ+3 : n=7 : 5 ; n=9 : 100 ; n=10 : 29 (dont 5 avec κ=1 ; n = 3σ+1 atteint) ; n=11 : 7 186 (tous n = 2σ+3).

Trous signalés : (i) le cas n ≥ 2σ+3 n'est pas prouvé ; (ii) le sous-cas n = 2σ+3, m = n−1, R = {x₀}, deg x₁ = deg x_m = σ avec une « case libre » J = {j₀} (Cas A2b du journal) a été analysé sans conclusion : on obtient seulement w ∈ F(x₁) avec N[w] = A := V(P) \ N[x₁] (|A| = σ+1), donc V = N[x₁] ⊔ N[w] ⊔ {x₀}, deux quasi-cliques ; contradiction non obtenue ; (iii) la borne n ≤ 3σ+1 n'est prouvée qu'en présence d'un sommet d'articulation (observée n ≤ 10).

## 5. Plan Lean (Théorème C)
Aucun résultat classique cité n'est utilisé comme boîte noire : Ore/Pósa sont réduits au Lemme 4 (cycle sur V(P) ⇒ chemin plus long) et à une rotation, prouvés sur place. Mathlib : `SimpleGraph.Walk.IsPath`, `IsHamiltonian`, `dist`, `Connected` existent ; pas d'Ore/Dirac/Pósa (à ma connaissance). À écrire : existence d'un plus long chemin (maximum fini), rotation, Lemme 4, Lemme 5 (insertion d'un sommet), comptages I₁/I_m (bijection i ↦ x_{i+1}), Fait 0 (lien `secondSmallestDegree`/`degreeSequence` ; le lemme existant `exists_distinct_degree_one_of_secondSmallestDegree_eq_one` est un cas particulier), Lemme 3, `distEven = 1 + |Γ|`. Estimation : 1 500–2 500 lignes pour le Théorème C ; Lemmes 1, 2, 6 : ~300–500 lignes chacun. Le théorème `conjecture189` complet reste hors de portée tant que §4 est ouvert ; énoncé formalisable intermédiaire : `conjecture189_of_card_le : Fintype.card α ≤ 2 * secondSmallestDegree G + 2 → …`.

## 6. Balayage n = 11 (histogramme n − 2σ)
Tous les graphes connexes n=11 (geng 8 tranches) : 27 429 222 vérifient (H). Histogramme n−2σ : −9:1, −7:29, −5:1 169, −3:112 195, −1:5 321 065, 1:21 987 577, **3:7 186**. Donc à n=11 le régime ouvert est exactement n = 2σ+3 (σ=4), 7 186 graphes (0,026 %) ; le Théorème C couvre les 27 422 036 autres. Les 603 357 graphes de (H) avec δ=1 ont tous n ≤ 2σ+2 (Cor. 1b confirmé). Max n−2σ observé : 2 (n≤6, 8), 3 (n=7, 9, 11), 4 (n=10).

## Manche 2

### M2.0 Feuille visée et statut
Feuille **R1.H1.R1.H2** (fichier `tree/…conjecture189.R1.H1.R1.lean`, `def H2`) : G connexe, `G.diam = 3`, δ+σ+1 < n, n ≤ (δ+1)(σ+1), (H), Hall sur les indépendants, ∃ triangle, δ ≥ 3 ⇒ chemin hamiltonien.
Statut : **réduite, non fermée**. Réglé : n ≤ 2σ+2 (Théorème C) et κ = 1 (Proposition K ci-dessous). Reste : κ ≥ 2, n ≥ 2σ+3, et un plus long cycle laisse une composante à ≥ 3 sommets (énoncé exact en M2.5).
En diamètre 3, (H) ⇔ |L₂(v)| ≤ σ pour tout v (seules distances paires : 0 et 2).

### M2.1 Données (balayages exhaustifs, scripts `r189/leaf.c`, `qstruct.py`, `inv.py`, `circ.c`, `checkK.py`)
- Graphes de la feuille : n ≤ 7 : 0 ; n=8 : 97 ; n=9 : 2 488 ; n=10 : 26 582 (balayage complet n ≤ 10, `geng -c -d3`) ; à n=11 seuls ceux du régime n ≥ 2σ+3 ont été extraits (n−2σ = 3 est le maximum à n=11, d'après le balayage complet de la manche 1).
- **Hors Théorème C** (n ≥ 2σ+3) : n=9 : 50 (κ=1:4, κ=2:37, κ=3:9) ; n=10 : 24 (κ=1:4, κ=2:17, κ=3:3) ; n=11 : 4 850 (κ=1:9, κ=2:361, κ=3:4 041, κ=4:439). n=9,10 : δ=σ=3 ; n=11 : σ=4, δ∈{3,4}.
- Classes structurelles (piste 1 du coordinateur) : **aucune structure commune**. Le quotient par jumeaux vrais varie de 4 à n sommets (n=9 : ≥ 40 classes WL distinctes pour 100 graphes du régime n ≥ 2σ+3) ; pas toujours de sommet simplicial (1 302/4 924 sans) ; « deux boules N[u] ∪ N[w] = V » faux pour 1 187/4 924. Les éclatés de cycles impairs ne sont qu'une sous-famille. ⇒ abandon de la piste « caractérisation ».
- Condition d'Ore à distance 2 (deg u + deg v ≥ n−1 si d(u,v)=2) : suffisante pour la traçabilité sur tous les graphes n ≤ 9, mais violée par 59/100 graphes du régime ouvert à n=9 ⇒ inutilisable.
- **Circonférence** : tout graphe 2-connexe vérifiant (H) a circonférence ≥ n−1 (exhaustif n ≤ 9 : 22 676 graphes ; régime ouvert n=11 : 7 139). Cible naturelle pour κ ≥ 2.
- Proposition K vérifiée structurellement sur les 22 graphes (25 sommets d'articulation) de diamètre 3, δ ≥ 2, (H), κ=1, n ≤ 10 : 0 échec.

### M2.2 Proposition K (diamètre 3 avec sommet d'articulation) — prouvée
**Énoncé.** G connexe, diam G = 3, δ ≥ 2, (H), G a un sommet d'articulation c ⇒ G traçable.
*Preuve.*
1. Lemme 6b (δ ≥ 2 exclut la composante {x₀}) : G − c a exactement deux composantes C₁, C₂.
2. Si chacune avait un sommet à distance ≥ 2 de c, ces deux sommets seraient à distance ≥ 4. Donc l'une, disons C₂, vérifie C₂ ⊆ N(c). Si aussi C₁ ⊆ N(c), diam ≤ 2 : exclu. Soit D = C₁ \ N(c) ≠ ∅ et N₁ = C₁ ∩ N(c) ≠ ∅. Tout d ∈ D est à distance exactement 2 de c (distance 3 ⇒ distance 4 à C₂).
3. Pour u ∈ N₁ : C₂ ⊆ L₂(u) (u ~ c ~ z, u ≁ z). Donc |C₂| ≤ σ. C₂ ≠ {x₀} (sinon deg x₀ = 1) ; pour z ∈ C₂ \ {x₀} : σ ≤ deg z ≤ |C₂| ⇒ |C₂| = σ et N[z] = C₂ ∪ {c}. Donc **C₂ ∪ {c} est une clique K_{σ+1}**, et L₂(u) = C₂ exactement pour tout u ∈ N₁.
4. Pour u ≠ u' dans N₁ : d(u,u') ≤ 2 (via c) et u' ∉ C₂ ⇒ u ~ u'. Donc **N₁ ∪ {c} est une clique**. Pour d ∈ D et u ∈ N₁ : d a un voisin u' ∈ N₁ (étape 2), donc d(u,d) ≤ 2 et d ∉ C₂ ⇒ u ~ d. Donc **N₁ est complet vers D**.
5. Soient k = |D|, q = |N₁| ≥ 1. On a L₂(c) = D, donc k ≤ σ. Pour d ∈ D : L₂(d) ⊇ {c} ∪ (D \ N[d]) (deux sommets de D ont un voisin commun dans N₁), d'où deg_D(d) ≥ k − σ. Pour d ≠ x₀ : N(d) ⊆ N₁ ∪ D ⇒ deg_D(d) ≥ σ − q. Deux sommets non adjacents de D (au plus un est x₀) ont une somme de degrés dans G[D] ≥ (k−σ) + (σ−q) = k − q.
6. **Ore (recouvrement par chemins)** : un graphe H à k sommets avec deg u + deg v ≥ k − q pour u ≁ v (q ≥ 1) se recouvre par ≤ q chemins disjoints. Preuve : H ∨ K_{q−1} vérifie la condition d'Ore pour les chemins (somme ≥ (k+q−1) − 1), donc est traçable (Ore 1960 : σ₂ ≥ N−1 ⇒ chemin hamiltonien) ; on retire les q−1 sommets ajoutés. Si k ≤ q, le recouvrement trivial suffit. Soit p ≤ q et Q₁,…,Q_p un recouvrement de D.
7. Chemin hamiltonien : (C₂ dans un ordre quelconque), c, (N₁ \ {n₁,…,n_p}), n₁, Q₁, n₂, Q₂, …, n_p, Q_p. Arêtes : clique C₂ ∪ {c} ; c ~ N₁ ; N₁ clique ; n_i ~ tout D. □
(Aucune hypothèse de triangle, de Hall ou n ≥ 2σ+3 n'est utilisée.)

### M2.3 Cas 2-connexe : plus long cycle C, composantes de G − C (lemmes prouvés)
Notations : C orienté, a⁺/a⁻ successeur/prédécesseur. Pour une composante K de G − C : A = N_C(K) ; faits classiques (cycle le plus long) : A ∩ A⁺ = ∅, A⁺ indépendant, A⁺ ∩ N(K) = ∅.
- **Lemme Cyc (composante singleton).** G 2-connexe, (H), C plus long cycle, y ∉ C avec N(y) ⊆ C et y ≠ x₀. Alors n = 2σ+1. En particulier, si n ≥ 2σ+2, les singletons de G − C sont ⊆ {x₀}.
 *Preuve.* k = deg y ≥ σ. N⁺(y) ∪ N⁻(y) ⊆ L₂(y), de taille 2k − g où g = #{a ∈ N(y) : a⁺⁺ ∈ N(y)} ; elle vaut ≥ k, avec égalité ssi |C| = 2k et y adjacent à un sommet sur deux. (H) : k ≥ σ ≥ |L₂(y)| ≥ k ⇒ égalité, k = σ, |C| = 2σ, L₂(y) = I := N⁺(y). Soit Z = V \ (C ∪ {y}). Aucun z ∈ Z n'est adjacent à N(y) (sinon z ∈ L₂(y) \ I), donc N_C(z) ⊆ I. Si Z ≠ ∅ : une composante K' de G[Z] a, par 2-connexité, deux attaches distinctes c₀, c_{2j} ∈ I (sinon y serait séparé de K' par un sommet) ; avec z ~ c₀, z' ~ c_{2j}, Q un chemin z'–z dans K', le cycle y c₁ c₂ … c_{2j} z' Q z c₀ c_{2σ−1} … c_{2j+1} y est plus long que C. Donc Z = ∅, n = 2σ+1. □
- **Lemme (**) (composante non triviale).** K composante, |K| ≥ 2, y ∈ K \ {x₀} avec c(y) := |N_C(y)| ≥ 1, k(y) := |N_K(y)|. Soient L(y) le nombre de « longs trous » (arcs entre voisins consécutifs de y sur C avec ≥ 2 sommets intérieurs), B_y = (A ∩ N(N_K(y))) \ N_C(y), K₂(y) = K ∩ L₂(y). Alors **L(y) + |B_y| + |K₂(y)| ≤ k(y)** et **L(y) ≥ 1**.
 *Preuve.* L₂(y) contient les ensembles disjoints N⁺(y) ∪ N⁻(y) (taille 2c − g = c + L), B_y (C-sommets hors A⁺), K₂(y). (H) et deg y = c + k ≥ σ ⇒ l'inégalité. Si L(y) = 0, |C| = 2c et A = N_C(y) (car C \ N_C(y) = N⁺ ⊆ A⁺) ; un autre z ∈ K attaché en a donnerait le cycle plus long … a z ⋯ y a⁺⁺ … ; donc y seul est attaché et c'est un sommet d'articulation, contradiction. □
- **Lemme (voisins privés).** Si a et a⁺⁺ sont voisins de y ∈ K, aucun autre sommet de K n'est adjacent à a ni à a⁺⁺ (sinon a y ⋯ z a⁺⁺ remplace a⁺ par ≥ 2 sommets).
- **Corollaire E (composantes à 2 sommets, et P₃).** En G 2-connexe avec (H), G − C n'a pas de composante K = {y,z} (arête) ni de composante isomorphe à P₃.
 *Preuve (arête).* Pour y ≠ x₀ : (**) avec k = 1 ⇒ L(y) = 1, B_y = ∅, donc N_C(z) ⊆ N_C(y). Si c(y) = 1, l'unique attache est un sommet d'articulation. Si c(y) ≥ 2, il y a un seul long trou, donc au moins un trou court (a, a⁺⁺). Si z ≠ x₀, symétriquement N_C(z) = N_C(y), et a y z a⁺⁺ remplace a⁺ : cycle plus long. Si z = x₀, tout voisin de y touche un trou court, donc est privé : N_C(z) = ∅ et deg z = 1, contradiction avec la 2-connexité. *(P₃ y–z–w)* : l'extrémité y ≠ x₀ a k = 1 et K₂(y) ∋ w ⇒ L(y) = 0, contradiction ; les deux extrémités ne peuvent pas être x₀ toutes deux. □

### M2.4 Conséquence : où en est la feuille
Pour G dans R1.H1.R1.H2 :
- n ≤ 2σ+2 : Théorème C ;
- κ = 1 : Proposition K ;
- κ ≥ 2 et n ≥ 2σ+3 : on prend un plus long cycle C. Si G − C ⊆ {x₀}, G est traçable (x₀ a un voisin sur C). Sinon G − C a une composante non singleton (Lemme Cyc), qui n'est ni une arête ni un P₃ (Corollaire E).

### M2.5 Énoncé exact du cas encore ouvert (feuille R1.H1.R1.H2)
G vérifie toutes les hypothèses de R1.H1.R1.H2, κ(G) ≥ 2, n ≥ 2σ+3, et il existe un plus long cycle C tel que G − V(C) a une composante K avec |K| ≥ 3 et K ≇ P₃. Il faut montrer que c'est impossible : alors circonférence ≥ n−1, donc traçable. Plus généralement, pour toute la conjecture en κ ≥ 2 (sans hypothèse de diamètre), le même énoncé sans « diam = 3 » suffit.
Outils disponibles : (**) pour chaque y ∈ K \ {x₀} attaché à C, voisins privés, 2-connexité. Piste suivante : récurrence sur |K| en prenant y ∈ K attaché qui maximise K₂(y), ou K clique (alors K₂ ≡ ∅ et deux attaches de sommets distincts de K sont à distance ≥ |K|+1 sur C).

### M2.6 Taille Lean (ajouts de la manche 2)
- Proposition K : 900–1 400 lignes. Le gros morceau est le théorème d'Ore pour les chemins et le recouvrement par chemins, absents de Mathlib (~500–700 lignes). Le reste est du calcul de distances en diamètre 3 et l'assemblage de listes (`flatten_block_chain` existe déjà dans le fichier de l'arbre).
- Lemmes Cyc, (**), voisins privés, Corollaire E : 1 000–1 500 lignes (rotations de cycles et insertion de sommets dans un cycle à écrire).

## Manche 3 — cible : G 2-connexe + (H) ⇒ circonférence ≥ n−1

### M3.0 Verdict
**Pas de preuve complète.** Acquis : les composantes de G − C (C plus long cycle) qui sont un singleton (≠ x₀), une arête ou un P₃ sont exclues (Manche 2). Le trou est le cas |K| ≥ 3, K ≇ P₃. Deux constructions montrent que la piste (1) « témoin local y ∈ K » est **fausse en diamètre quelconque**. Elle reste plausible en diamètre 3 (version faible, voir M3.4).

### M3.1 Tests (scripts `r189/witness.c`, `witness2.c`, `witness3.c` : énumération de TOUS les plus longs cycles)
Pour chaque graphe 2-connexe de circonférence ≤ n−2, chaque plus long cycle C et chaque composante K de G − C avec |K| ≥ 2 :
- n=8 : 171 graphes, 264 couples (C,K) ; n=9 : 2 349 graphes, 3 688 couples ; **n=10 : 53 482 graphes, 85 100 couples** (balayage complet `geng -C 10`).
- Dans **tous** les cas, il existe y ∈ K avec |L₂(y)| ≥ deg(y)+1 (version purement structurelle, sans (H)), et même au moins deux tels y (n ≤ 9) ; *a fortiori* |L₂(y)| > σ.
- Tester le témoin dans K ∪ A⁺ ∪ A n'apporte rien de plus jusqu'à n=10.

### M3.2 Les deux renforcements locaux sont faux au-delà de n=10
- **Structurel (|L₂(y)| > deg y pour un y ∈ K) faux à n=11.** K = K₃ ; a, b adjacents à tout K ; deux arcs a–p₁–p₂–p₃–b et a–q₁–q₂–q₃–b. La circonférence vaut 8 = n−3 (trois branches entre a et b). Pour y ∈ K : deg y = 4 = |L₂(y)|. (Ici σ = 2, donc la version avec σ tient encore.)
- **Version avec σ, et même avec Γ (distances paires), pour y ∈ K : fausse à n=15.** θ-graphe de cliques : K = K_s, a et b complets vers K, P = K_r avec p₀ ~ a et p_{r−1} ~ b, Q = K_r de même, s < r. Avec (s,r) = (3,5), (4,6), (5,7), soit n = 15, 18, 21 : 2-connexe, circonférence n − s, **|Γ(y)| = 4 ≤ σ pour tout y ∈ K**. (H) n'échoue que sur les sommets des arcs P, Q (12 à 16 sommets), via des sommets à distance **4**.
- ⇒ En diamètre quelconque, une preuve doit utiliser (H) sur des sommets de C et la parité au-delà de la distance 2. Les arguments du type (\*\*) centrés sur K ne suffisent pas.

### M3.3 Ce qui est prouvé (rappel, valable en diamètre quelconque, G 2-connexe, (H))
Lemme Cyc (singleton ≠ x₀ ⇒ n = 2σ+1, et alors circonférence = n−1) ; inégalité (\*\*) ; voisins privés ; Corollaire E (pas d'arête ni de P₃). Le cas triangle (K = K₃) a été poussé : si deux sommets de K différents de x₀ ont des voisins sur C, on a c(u), c(v) ≤ 2 et σ ≤ 4 ; la suite demande une analyse des cordes des arcs (≥ 3 sommets intérieurs entre attaches de sommets distincts), non terminée.

### M3.4 Énoncé minimal ouvert
**Version forte (toute la conjecture, cas 2-connexe)** : G 2-connexe, (H), C plus long cycle ⇒ G − V(C) n'a aucune composante K avec |K| ≥ 3, K ≇ P₃. Ce qui est prouvé (M3.3) donne alors circonférence ≥ n−1, donc G traçable.
**Version faible (feuille R1.H1.R1.H2, diamètre 3, donc Γ = L₂)** : G 2-connexe, diam G = 3, C plus long cycle, K composante de G − C avec |K| ≥ 3, K ≇ P₃ ⇒ ∃ y ∈ K avec |L₂(y)| > σ.
- Vérifiée sans contre-exemple : exhaustif n ≤ 10, plus 119 130 θ-graphes de cliques de diamètre 3 (n ≤ 24 ; s ≤ 6, arcs ≤ 8, attaches variables), aucun ne satisfaisant |L₂| ≤ σ sur K.
- Les contre-exemples de M3.2 ont diamètre 4 : en diamètre 3, chaque sommet d'arc est à distance ≤ 3 de K, ce qui force a et b à avoir beaucoup de voisins sur les arcs, d'où |L₂(y)| grand pour y ∈ K.
- Avec la version faible, la feuille R1.H1.R1.H2 est entièrement close : Théorème C + Proposition K + Lemmes Cyc et E + version faible.

### M3.5 Lean
Si la version faible est prouvée : ~1 500–2 500 lignes de plus que les manches 1–2 (plus long cycle, insertion d'un chemin de K dans un arc, comptage des trous). Les constructions de M3.2 sont des certificats finis (n = 11 et 15), vérifiables par `decide` sur `Fin n`, si l'on veut documenter l'échec de la piste locale.

## Étape H1 — sommet d'articulation (feuille `H1` du fichier R2) : **PROUVÉE**

### H1.0 Énoncé et verdict
`H1` : G connexe, n ≥ 2, (H), 2σ+3 ≤ n, ∃ c avec G − c non connexe ⇒ G traçable. **Preuve complète ci-dessous**, valable en diamètre quelconque, sans Ore, sans Proposition K. On prouve en fait plus : **(H) + δ ≥ 2 + sommet d'articulation ⇒ traçable** (l'hypothèse n ≥ 2σ+3 ne sert qu'à obtenir δ ≥ 2). Avec le Théorème C : (H) + sommet d'articulation ⇒ traçable, pour tout n. La Proposition K (M2.2) devient un corollaire et n'a plus à être formalisée.
Idée clé : prendre P **le plus long parmi les chemins qui contiennent x₀**. Toutes les opérations des Lemmes 4 et 5 (prolongement, rotation, insertion, ouverture d'un cycle) produisent des chemins dont l'ensemble de sommets contient V(P), donc contient x₀ : ces lemmes restent vrais. Et le sommet x₀ (degré petit) n'est jamais hors du chemin, ce qui supprime le seul cas qui résistait au comptage.

### H1.1 Lemmes (G connexe, (H), x₀ de degré minimum, Fait 0 : deg v ≥ σ pour v ≠ x₀)
**H1.1 (δ ≥ 2).** Si n ≥ 2σ+3 alors δ ≥ 2, donc σ ≥ 2. *Preuve.* Cor. 1b : une feuille x₀ de voisin c' donne E(x₀)+E(c') = n (pour tout w, d(x₀,w) = 1 + d(c',w) si w ≠ x₀), d'où n ≤ 2σ+2. □
Dans la suite : δ ≥ 2 (et σ ≥ δ ≥ 2), c sommet d'articulation.
**H1.2 (géométrie d'un sommet d'articulation).** Soit C une composante de G − c. (a) v ∈ C ⇒ N(v) ⊆ C ∪ {c}. (b) C ∩ N(c) ≠ ∅. (c) u ∈ C, w ∉ C ∪ {c} ⇒ d(u,w) = d(u,c) + d(c,w). (d) u ∈ C ∩ N(c), z ∈ C' ∩ N(c), C' ≠ C ⇒ d(u,z) = 2. □ (élémentaire)
**H1.3 (Lemme 6).** (a) n ≤ 3σ+1 ; (b) G − c a exactement deux composantes C₁, C₂. (Preuves en §2.)
**H1.4 (tailles).** σ ≤ |Cᵢ| ≤ 2σ. *Preuve.* |Cᵢ| ≥ 2 (un singleton {z} aurait deg z = 1 < δ), donc Cᵢ contient z ≠ x₀ avec N(z) ⊆ (Cᵢ\{z}) ∪ {c} : σ ≤ |Cᵢ|. Puis |Cᵢ| = n − 1 − |C_{3−i}| ≤ 3σ − σ. □
**H1.5 (D2 : diamètre 2 hors x₀).** p ≠ r dans Cᵢ \ {x₀} ⇒ d(p,r) ≤ 2. *Preuve.* Sinon N[p] ∩ N[r] = ∅, deux ensembles de taille ≥ σ+1 dans Cᵢ ∪ {c} : |Cᵢ| ≥ 2σ+1, contre H1.4. □
**H1.6 (côté minimal).** Si |C'| = σ et x₀ ∉ C' alors C' ⊆ N(c) (et C' ∪ {c} est une clique). *Preuve.* z ∈ C' : deg z ≥ σ = |(C'\{z}) ∪ {c}| ⊇ N(z), égalité. □
**H1.7 (cas limite, lemme de contradiction).** Si |Cᵢ| = 2σ, alors aucun v ∈ Cᵢ ∩ N(c), v ≠ x₀, n'a deg v = σ.
*Preuve.* |C_{3−i}| = σ (H1.3a, H1.4). U = Cᵢ \ N[v] a 2σ − 1 − (σ−1) = σ éléments ; ceux ≠ x₀ sont à distance 2 de v (H1.5) ; N(c) ∩ C_{3−i} est à distance 2 de v (H1.2d) et disjoint de U. Si x₀ ∉ Cᵢ : |Γ(v)| ≥ σ + 1. Si x₀ ∈ Cᵢ : x₀ ∉ C_{3−i}, donc |N(c) ∩ C_{3−i}| = σ (H1.6) et |Γ(v)| ≥ (σ−1) + σ ≥ σ+1 (σ ≥ 2). Contredit (H). □
**H1.8 (plus long chemin passant par x₀).** Soit 𝒫 l'ensemble des chemins contenant x₀ et P = x₁…x_m ∈ 𝒫 de longueur maximale dans 𝒫 ; supposons m < n. Alors :
(a) [Lemme 4 dans 𝒫] N(x₁), N(x_m) ⊆ V(P), I₁ ∩ I_m = ∅, deg x₁ + deg x_m ≤ m − 1 ;
(b) [Lemme 5ab dans 𝒫] y ∉ V(P), y ~ x_j ⇒ 2 ≤ j ≤ m−1, y ≁ x_{j±1}, x₁ ≁ x_{j+1}, x_m ≁ x_{j−1} ;
(c) [rotation] on peut choisir P avec x₁, x_m ≠ x₀ (si x₁ = x₀ : deg x₀ ≥ 2 et (a) donnent x₀ ~ x_j, j ≥ 3 ; x_{j−1}…x₂x₁x_j…x_m ∈ 𝒫, même longueur) ;
(d) alors m ≥ 2σ + 1 ; et tout y ∉ V(P) est ≠ x₀, donc deg y ≥ σ.
*Preuve.* Mêmes constructions que les Lemmes 4, 5 : chaque chemin construit contient V(P) ∋ x₀, donc est dans 𝒫. □
**H1.9 (position de c).** Sous H1.8(c) : c = x_k avec 2 ≤ k ≤ m−1, et {x₁,…,x_{k−1}} ⊆ C₁, {x_{k+1},…,x_m} ⊆ C₂ (à renommage près).
*Preuve.* c ∉ V(P) ⇒ P dans une composante, m ≤ 2σ : exclu par H1.8(d). c = x₁ ⇒ x₂…x_m dans une composante C, or c a un voisin dans l'autre (H1.2b), hors de P : contredit H1.8(a). Si les deux segments sont dans la même composante C : m ≤ |C| + 1 ≤ 2σ+1, donc égalité : |C| = 2σ, V(P) = C ∪ {c}, deg x₁ = deg x_m = σ, I₁ ⊔ I_m = [1, m−1]. Un y ∈ N(c) ∩ C' (C' l'autre composante) est hors de P et y ~ x_k : par H1.8(b), k−1 ∉ I_m, donc k−1 ∈ I₁, i.e. x₁ ~ c. Alors x₁ ∈ C ∩ N(c), x₁ ≠ x₀, deg x₁ = σ, |C| = 2σ : contredit H1.7. □
**H1.10 (comptage).** Dans la configuration H1.9, pour tout y ∈ C₁ \ V(P) : **deg x₁ + deg y ≤ |C₁| − 1 + [y ~ c]**.
*Preuve.* N(x₁) ⊆ {x₂,…,x_k} (H1.8a, H1.2a), donc I₁ ⊆ [1,k−1], |I₁| = deg x₁. N(y) ∩ V(P) = {x_j : j ∈ J}, J ⊆ [2,k] (H1.8b, H1.2a). Pour j ∈ J' := J ∩ [2,k−1] : x₁ ≁ x_{j+1}, i.e. j ∉ I₁. Donc |I₁| + |J'| ≤ k − 1 = |C₁| − |R₁| (R₁ = C₁ \ V(P)). Et deg y ≤ |J'| + [y ~ c] + (|R₁| − 1). On somme. □
**H1.11 (conclusion).** Si y ∈ R₁ : H1.10 + H1.8(d) donnent 2σ ≤ |C₁| − 1 + [y~c] ≤ 2σ − 1 + [y~c], donc y ~ c, |C₁| = 2σ et deg y = σ : contredit H1.7 (y ≠ x₀). Donc R₁ = ∅ ; de même R₂ = ∅ (P renversé est dans 𝒫, mêmes hypothèses). Par H1.3b, V = C₁ ∪ C₂ ∪ {c} ⊆ V(P) : m = n, contradiction. Donc le plus long chemin de 𝒫 est hamiltonien. **H1 est démontrée.** □

### H1.2 Réponses aux trois questions du brief
1. **Structure « clique K_{σ+1} d'un côté » : fausse sans diamètre 3.** Contre-exemples de diamètre 4 : `HCdbBNp`, `HCdbEhf`, `HQhTQjw` (n=9), `J?ouPjILT{?` (n=11) : aucun côté C ∪ {c} n'est une clique. Elle ne vaut que dans le cas limite |C'| = σ, x₀ ∉ C' (H1.6). Elle n'est plus utilisée.
2. **Diamètre.** diam ≥ 3 est prouvé (Cor. 2a : diam ≤ 2 ⇒ n ≤ 2σ+1). Observé : ecc(c) ≤ 2 dans chaque composante pour les 70 graphes de H1 (n ≤ 11) et pour les 1 630 « côtés » enracinés admissibles à ≤ 8 sommets ; d'où diam ∈ {3, 4}, et le diamètre 4 est atteint (n = 7, 9, 10, 11 ; 49 des 70 graphes). Une preuve de ecc(c) ≤ 2 a été esquissée (D2 + comptages de Γ par parité), **non rédigée ni relue** : inutile pour H1.
3. **Ore / recouvrement par chemins : inutile pour H1.** Pour mémoire (Prop. K, étape 6) : *si H a k sommets et deg u + deg v ≥ k − q pour u ≁ v (q ≥ 1), V(H) se recouvre par ≤ q chemins disjoints.* Preuve courte : H ∨ K_{q−1} (N = k+q−1 sommets) a σ₂ ≥ (k−q) + 2(q−1) = N − 1 ; il est connexe, et un plus long chemin non hamiltonien contredirait le Lemme 4 (deg x₁ + deg x_m ≤ m − 1 ≤ N − 2 avec x₁ ≁ x_m) ; on retire les q−1 sommets ajoutés. En Lean ce serait `lemma4` appliqué au joint. Mais la Prop. K est désormais un cas particulier de H1.0 (elle suppose δ ≥ 2).

### H1.3 Vérifications numériques (scripts `wowii/h1/`)
- `verh1.py` : les **70 graphes de H1 pour n ≤ 11** (n=7:3, 9:15, 10:5, 11:47), 182 choix de x₀ × sommets d'articulation : δ ≥ 2, n ≤ 3σ+1, exactement 2 composantes, σ ≤ |Cᵢ| ≤ 2σ, D2, H1.6, prémisse de H1.7 jamais réalisée, plus long chemin de 𝒫 hamiltonien : **0 violation**.
- `core.py`, `core2.py` (sans (H), tous les graphes connexes avec sommet d'articulation, n ≤ 9, tout x₀ de degré min., **tous** les plus longs chemins de 𝒫) : H1.8(a)(b)(c) et l'inégalité H1.10 (17 992 cas pour n=9, 960 pour n=8) : **0 violation**. (Une première version du test codait à tort « |C₁| ≥ 2σ » sans l'hypothèse |C₁| ≤ 2σ : 176 « violations » à n=8, toutes conformes à l'énoncé correct |C₁| ≥ 2σ+1−[y~c].)
- `pureF.py` (sans (H)) : D2, H1.6, H1.7 sur graphes recollés |C| = 2σ, |C'| = σ, σ = 2, 3 (12 177 graphes, 29 026 cas H1.7) : **0 violation**.
- `glue.py` (énumération exacte de H1 par recollement de deux côtés au sommet c ; (H) se découple : Γ(v) = Γ_{B₁}(v) + o₂ ou e₂, Γ(c) = E₁ ∪ E₂) ; validée par `gluex.py` qui retrouve exactement les classes connues (n = 7, 9, 10). **n = 12 (σ=4) et n = 13 (σ = 4, 5) : 0 graphe non traçable** (291, 122, 469 graphes étiquetés).
- `side.py` : lemme « côté » isolé (B enraciné en c, contraintes (H) découplées) : chemin hamiltonien depuis c pour les 1 630 côtés admissibles à ≤ 8 sommets.

### H1.4 Plan Lean (estimation)
| Lemme | Contenu | Lignes |
|---|---|---|
| H1.1 | feuille ⇒ n ≤ 2σ+2 (identité E(x₀)+E(c') = n) | 80–150 |
| H1.2 | composantes de `G.induce {x ∣ x ≠ c}`, voisinages, d(u,w) = d(u,c)+d(c,w) | 250–400 (le coût principal) |
| H1.3 | Lemme 6a, 6b (comptage de Γ) | 200–300 |
| H1.4–H1.6 | tailles, D2, côté minimal | 150–250 |
| H1.7 | contradiction cas limite | 120–200 |
| H1.8 | famille 𝒫 : `exists_longest` avec prédicat ; `lemma4`, `lemma5ab` avec `hmax` restreint aux listes contenant V(l) ; rotation | 150–300 (surtout adaptation) |
| H1.9–H1.11 | position de c, comptage, assemblage | 300–500 |
Total ≈ **1 250–2 100 lignes**. Réutilisé du fichier R2 : `degree_pair` (Fait 0), `exists_longest`, `lemma4`, `lemma5ab` (en remplaçant l'hypothèse `hmax` « tout chemin » par « tout chemin dont les sommets contiennent ceux de l », plus faible, que les preuves existantes devraient déjà satisfaire, à vérifier), `dist_two`, `lemma3a`, `rot`, `ham_of_list`, `getD_*`, le schéma de rotation de `caseB_aux`. Non nécessaires : `lemma5c`, `lemma3b`, `caseA`, `theorem_C`, Ore, Proposition K.

## Étape H2 — cas 2-connexe (feuille `H2` du fichier R2) : **réduite à n ≥ 2σ+5, non close**

### H2.0 Verdict
Pas de preuve complète de H2. **Prouvé (nouveau)** : **Théorème D** : G connexe, (H), **n ≤ 2σ+4** ⇒ traçable (sans 2-connexité ; donc vaut aussi pour H1). Pour n = 2σ+5 il ne reste que : P plus long chemin contenant x₀, m = 2σ+2, G − V(P) = un triangle. H2 reste ouvert pour n ≥ 2σ+5. Réduction structurelle : **Claim C ⇒ H2 pour tout n**, Claim C vérifié exhaustivement (2-connexes, n ≤ 10).
Scripts et sorties : `wowii/h2/` (`lp*.c`, `cl*.c`, `hc.c`, `tight.c`, `chk.py`, `t1.py`, `t3.py`).

### H2.1 Cadre « x₀-plus long » (astuce de l'Étape H1)
P = x₁…x_m est **le plus long parmi les chemins contenant x₀** ; R = V \ V(P), donc **x₀ ∉ R** et tout sommet de R a degré ≥ σ (Fait 0). Les Lemmes 4, 5a–c, (R4), (R6) restent vrais pour P (leurs opérations — prolongement, rotation, insertion, ouverture d'un cycle sur V(P) — donnent des chemins ⊇ V(P) ∋ x₀ ; (R4) et (R6) n'utilisent en plus que le Lemme 6a). Si x₀ = x₁ et deg x₀ ≥ 2, x₀ ~ x_j (j ≥ 3) et la rotation x_{j−1}…x₂x₀x_j…x_m garde V(P) : on suppose x₁, x_m ≠ x₀. En régime n ≥ 2σ+3 (δ ≥ 2) et G non traçable : **m ≥ 2σ+2**, donc |R| ≤ n − 2σ − 2.
*Mise en garde* : une opération qui **retire** un sommet x_i de P n'est licite que si x_i ≠ x₀.

### H2.2 Lemme P (composante de G − P, version chemin de (**))
K composante de G[R], y ∈ K avec c(y) := |N_P(y)| ≥ 1, k(y) := |N_K(y)|, K₂(y) := K ∩ L₂(y), B_y := N_P(K \ {y}) \ N_P(y).
(a) [insertion] si y ~ x_j et u ∈ K \ {y} alors u ≁ x_{j±1} (sinon x_j y ⋯ u x_{j±1} insère ≥ 2 sommets).
(b) Γ(y) ⊇ N_P(y)^± ⊔ K₂(y) ⊔ B_y, avec |N_P(y)^±| = 2c(y) − #{j : j, j+2 ∈ J_y} ≥ c(y)+1 (égalité ssi J_y est une progression de pas 2) ; les trois ensembles sont à distance exactement 2 de y et disjoints par (a).
(c) (H) et deg y = c + k ≥ σ ⇒ **1 + |K₂(y)| + |B_y| ≤ k(y)**.
*Corollaire.* G − P n'a pas de composante singleton (k = 0 : Lemme 5c) ni **P₃** (extrémité u : k = 1, c ≥ 1 car deg u ≥ σ ≥ 2, et K₂(u) ∋ w).

### H2.3 Lemme E′ (pas de composante arête)
G − P n'a pas de composante K = {y, z}. *Preuve.* c(y) ≥ 1 (sinon deg y = 1 < δ). (c) avec k = 1 : B_y = ∅, |N_P(y)^±| = c(y)+1 = σ (car σ ≥ |Γ(y)| ≥ c+1 et c + 1 = deg y ≥ σ), donc N_P(z) ⊆ N_P(y), J_y progression de pas 2 ; symétriquement N_P(y) = N_P(z) =: {x_j, x_{j+2}, …, x_{j+2(c−1)}}, c = σ − 1.
- c ≥ 3 : parmi les c−1 ≥ 2 trous x_{i+1} (i, i+2 ∈ J), l'un est ≠ x₀ ; x₁…x_i z y x_{i+2}…x_m contient x₀ et a m+1 sommets. Contradiction.
- c = 2 (σ = 3) : seul trou x_{j+1} ; s'il est ≠ x₀, idem. S'il vaut x₀ : x₀ ≁ x_{j−1} (sinon x₁…x_{j−1}x₀x_j y z x_{j+2}…x_m, m+2 sommets) et x₀ ≁ x_{j+3} (symétrique) ; donc y, z, x_{j−1}, x_{j+3} ∈ L₂(x₀) : |Γ(x₀)| ≥ 4 > σ. Contradiction.
- c = 1 (σ = 2) : x_j sépare {y,z} du reste ⇒ n ≤ 3σ+1 = 7 (Lemme 6a), or n ≥ m+2 ≥ 2σ+4 = 8. □

### H2.4 Théorème D (n ≤ 2σ+4)
G connexe, (H), n ≤ 2σ+4 ⇒ G traçable. *Preuve.* n ≤ 2σ+2 : Théorème C. Sinon δ ≥ 2 (Cor. 1b) ; si G n'est pas traçable, P x₀-plus long (H2.1) a m ≥ 2σ+2, donc |R| ≤ 2 et x₀ ∉ R ; une composante de G[R] est un singleton (Lemme 5c) ou une arête (Lemme E′) : contradiction. □
**Conséquence n = 2σ+5** : m ∈ {2σ+2, …}, |R| ≤ 3 ; singletons, arêtes, P₃ exclus ⇒ seul reste **m = 2σ+2, G[R] = K₃** (et σ ≥ 4 : n ≤ 11 est couvert par le balayage exhaustif, et n = 11 n'a aucun graphe de (H) avec σ = 3). Contraintes déjà obtenues pour K = {u,v,w} (Lemme P, σ ≥ 4) : c(y) ∈ {σ−2, σ−1}, |A| ≤ σ−1 (A = N_P(K)), chaque y voit tout A sauf ≤ 1 sommet ; si un y a c(y) = σ−1, deux attaches consécutives d'écart 2 portées par deux sommets distincts de K et un trou ≠ x₀ donnent x_p y v' y' x_{p+2} (m+2 sommets) : contradiction. Donc deg y = σ pour y ∈ K ; deux attaches consécutives de A portées par deux sommets distincts sont à distance ≥ 4 sur P sauf le trou contenant x₀. Non terminé.

### H2.5 Faits auxiliaires (plus longs chemins globaux, R = {x₀})
Valables si un plus long chemin (global) a m = n−1 sommets : (F1) tout plus long chemin manque exactement x₀ (Lemme 5c) ; (F2) x₀ ≁ q₂, q_{m−1} pour tout plus long chemin Q ; (F3) x₀ ~ x_j ⇒ x₁ ≁ x_{j+1}, x_{j+2} et x_m ≁ x_{j−1}, x_{j−2}. (G) Avec Z = [1, m−1] \ (I₁ ∪ I_m) : si j < j' ∈ N_P(x₀), x₁ ~ x_j et x_m ~ x_{j+1}, alors x_{j−1}…x₁x_jx₀x_{j'} + cycle x_{j+1}…x_mx_{j+1} est hamiltonien (symétrique pour j' < j) ; donc j ≠ max ⇒ Z ∩ {j±1} ≠ ∅, j ≠ min ⇒ Z ∩ {j−2, j} ≠ ∅, et **d₁ + d_m ≤ m − 2**. Cela donne une seconde preuve (par configurations) du cas n = 2σ+3 et ferme le « trou (ii) » de la §4 ; constructions testées aléatoirement (`chk.py` : 9 719 instances, 0 échec).

### H2.6 Réduction structurelle : Claim C (angle 1)
**Claim C.** G 2-connexe non traçable, P plus long chemin (global) d'extrémités x₁, x_m ⇒ max(|Γ(x₁)|, |Γ(x_m)|) ≥ σ+1. Claim C contredit (H) directement : **Claim C ⇒ H2 pour tout n** (sans n ≥ 2σ+3). Variante plus faible suffisante : Claim A (un plus long chemin a une extrémité avec |Γ| > σ).
Tests (exhaustifs, `nauty-geng -C`) : n ≤ 9 : 0 échec ; **n = 10 : 9 743 542 graphes 2-connexes, 36 076 non traçables, 0 échec de C, A, et de B** (une extrémité v avec |Γ(v)| > deg v). Recherche locale (`hc.c`, n = 12, 13, 14) : marge minimale 1, aucun contre-exemple.
- La 2-connexité est nécessaire : C échoue sur des graphes connexes (n = 7 : 1, n = 8 : 8).
- **Versions locales fausses à n = 10** (vraies n ≤ 9) : σ remplacé par le 2e plus petit degré de {x₁, x_m} ∪ R (56 chemins), par min_{y∈R} deg y (192), |Γ(x₁)|+|Γ(x_m)| ≥ 2deg y+1 (256), « une extrémité a |Γ| > son degré » (34 graphes), et pour m = n−1 « max|Γ| > min(d₁,d_m) » (28). Exemple `I?`CQJw|?` : σ = 2 est atteint par des extrémités de rotation (sommets 6, 7) **sur** P. Une preuve de C doit donc utiliser le σ global (rotations de Pósa), pas seulement x₁, x_m, R.

### H2.7 Angles 2 et 3 (données, n ≤ 11)
- Tous les graphes 2-connexes du régime n ≥ 2σ+3 sont **hamiltoniens** (n = 7 : 2, 9 : 85, 10 : 24, 11 : 7 139) et contiennent un triangle (n = 9, 11).
- Hérédité (n = 11, 7 139 graphes 2-connexes) : G − x₀ vérifie (H) pour 6 686 (453 échecs) ; un G − v vérifie (H) : 6 981 (158 échecs), dont seulement 435 restent dans le régime ; une contraction d'arête préserve (H) : 7 123 (16 échecs). Pas de récurrence naturelle.

### H2.8 Trou exact
H2 restant : G 2-connexe, (H), **n ≥ 2σ+5**. Énoncé minimal (cadre x₀-plus long) : aucune composante K de G − V(P) avec |K| ≥ 3, K ≇ P₃ (tous ses sommets de degré ≥ σ, ≥ 2 attaches). Premier cas ouvert : n = 2σ+5, K = K₃, m = 2σ+2, σ ≥ 4. Alternative globale : prouver Claim C (ou A).
Lean : Théorème D ≈ Théorème C + 400–700 lignes (cadre x₀-plus long partagé avec H1, Lemme P(a–c), Lemme E′).

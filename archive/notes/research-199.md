# WOWII 199 — recherche de preuve (journal factuel)

Verdict : **preuve partielle**. Prouvé : cas κ ≤ 1, cas maille ≥ 5 (sans C3 ni C4), cas sans griffe (via théorèmes profonds).
Réduction prouvée : Conjecture 199 ⇐ (Lemme L+) ∧ (Lemme de couche), deux énoncés plus petits, vérifiés numériquement, NON prouvés.
Scripts / sorties : `scratchpad/wowii/r199/` (C + nauty-geng, invariants comme en Lean).

## 0. Conventions (Lean)
- t = largestInducedTreeSize, κ = vertexConnectivity (K_n : κ = n−1), α = nombre d'indépendance.
- G connexe, n ≥ 2 ⇒ t ≥ 2 (une arête) et κ ≥ 1. Hypothèse `t − 2 ≤ κ` (ℕ) ⟺ t ≤ κ + 2.
- But contraposé (C) : G connexe **non traçable** ⇒ t ≥ κ + 3.
- F0. Les arbres induits sont stables par suppression d'une feuille ; donc t ≥ r ⇒ il existe un arbre induit d'ordre exactement r.
- F1. κ ≤ δ (si G non complet, v de degré δ < n−1 : G − N(v) est non connexe ; si G = K_n, κ = n−1 = δ).

## 1. Résultats classiques utilisés (énoncés exacts)
- [CE] Chvátal–Erdős (Discrete Math. 2, 1972) : tout graphe à ≥ 3 sommets avec α ≤ κ est hamiltonien.
  [CE-chemin] Corollaire : G (n ≥ 2) avec α ≤ κ + 1 a un chemin hamiltonien (appliquer [CE] à G ∨ K1 : κ+1, même α).
- [B] Bedrossian (thèse 1991 ; Faudree–Gould, Discrete Math. 173, 1997) : tout graphe 2-connexe {K_{1,3}, P_6}-libre est hamiltonien.
- [ŁP] Łuczak–Pfender (J. Graph Theory 47, 2004, 111–121) : tout graphe 3-connexe {K_{1,3}, P_11}-libre est hamiltonien.
- [KV] Kaiser–Vrána (European J. Combin. 33, 2012 ; arXiv 1009.3754) : tout graphe sans griffe 5-connexe de degré minimum ≥ 6 est hamiltonien (énoncé pour les graphes adjoints, étendu aux sans-griffe dans l'article).

## 2. Lemmes prouvés (élémentaires, formalisables)
**L1 (géodésique).** diam(G) ≥ κ + 2 ⇒ t ≥ κ + 3. Preuve : un plus court chemin est induit (déjà en Lean : `Walk.induce_support_isTree_of_length_eq_dist`).

**L2 (étoile).** Si un sommet v a κ + 2 voisins deux à deux non adjacents, t ≥ κ + 3 (étoile induite K_{1,κ+2}).

**L3 (séparateur minimum à beaucoup de composantes).** Si S est un ensemble séparant avec |S| = κ et G − S a c ≥ κ + 2 composantes, alors t ≥ κ + 3.
Preuve : tout s ∈ S a un voisin dans chaque composante D (sinon D est une composante de G − (S − s), qui est non connexe avec |S − s| = κ − 1, contradiction avec la définition de κ). Un voisin de s par composante : étoile induite à c + 1 ≥ κ + 3 sommets. ∎

**L4 (t ≥ min(α, 4)).** G connexe et α ≥ 3 ⇒ G contient un P4 ou un K_{1,3} induit, donc t ≥ 4.
Preuve : {a, b, c} indépendant. Si deux d'entre eux sont à distance ≥ 3, une géodésique donne un P4 induit. Sinon toutes les distances valent 2. Soit p voisin commun de a, b. Si p ~ c : griffe en p. Sinon soit q voisin commun de a, c (q ≠ p). Si q ~ b : griffe en q. Sinon, si q ~ p : c–q–p–b est un P4 induit (c≁p, c≁b, q≁b) ; si q ≁ p : b–p–a–q est un P4 induit (b≁a, b≁q, p≁q). ∎

**L5 (double étoile).** Si G n'a ni C3 ni C4 (sous-graphe) et uv ∈ E, alors G[N[u] ∪ N[v]] est un arbre à deg(u) + deg(v) sommets.
Preuve : pas de voisin commun (C3) ; aucune arête dans N(u) ou N(v) (C3) ; une arête x y avec x ∈ N(u)−v, y ∈ N(v)−u donne le C4 u x y v. ∎

## 3. Théorèmes partiels prouvés
**T1 (κ ≤ 1).** G connexe, n ≥ 2, κ = 1, t ≤ 3 ⇒ G traçable. Plus fort : tout G connexe avec t ≤ 3 est traçable.
Preuve : t ≤ 3 ⇒ α ≤ 2 (L4) ≤ κ + 1 ⇒ [CE-chemin]. ∎ (Donc tout contre-exemple a κ ≥ 2.)

**T2 (sans C3 ni C4, y compris les arbres).** La conjecture 199 est vraie. Preuve sans [CE] :
si Δ ≤ 2, G connexe est un chemin ou un cycle, traçable. Si Δ ≥ 3, prendre u de degré Δ, v ∈ N(u) : L5 donne t ≥ Δ + deg(v) ≥ 3 + δ ≥ 3 + κ (F1), donc l'hypothèse t ≤ κ + 2 est fausse. ∎

**T3 (sans griffe).** La conjecture 199 est vraie pour les graphes sans K_{1,3} induit.
Preuve : un arbre induit ayant un sommet de degré ≥ 3 contient une griffe induite ; donc t = ordre du plus long chemin induit et l'hypothèse ⟺ G est P_{κ+3}-libre.
κ = 1 : T1. κ = 2 : P5-libre ⇒ P6-libre ⇒ hamiltonien [B]. 3 ≤ κ ≤ 8 : κ + 3 ≤ 11 ⇒ P11-libre, 3-connexe ⇒ hamiltonien [ŁP]. κ ≥ 6 : 5-connexe, δ ≥ κ ≥ 6 ⇒ hamiltonien [KV]. ∎ (Non formalisable à coût raisonnable.)

**T4 (structure de la couche α = κ + 2, prouvée).** G connexe non traçable, κ = k, α = k + 2. P = v1…vm plus long chemin, H composante de G − V(P), X = N(H), x⁺ successeur sur P.
- (P1) v1, vm ∉ X. (P2) x ∈ X ⇒ x⁺, x⁻ ∉ X (insérer un chemin de H). (P3) x < y dans X ⇒ x⁺ ≁ y⁺ (chemin v1…x, H, y, y⁻…x⁺, y⁺…vm). (P4) v1 ≁ x⁺ (chemin H, x, x⁻…v1, x⁺…vm).
- Donc A_h = {h, v1} ∪ X⁺ est indépendant (|X| + 2 sommets) pour tout h ∈ H ⇒ |X| ≤ k ; X sépare H de v1 ⇒ |X| ≥ k. **|X| = k, X séparateur minimum, A_h indépendant maximum** (donc dominant). Idem A⁻_h = {h, vm} ∪ X⁻.
- (P7) H est une clique (h' ∈ H − h doit avoir un voisin dans A_h ; seul h est possible).
- (P8) Chaque composante de G − X contient un sommet de A_h (A_h dominant et disjoint de X) ⇒ c(G − X) ≤ k + 2, avec égalité ⟺ les k+2 sommets de A_h sont dans des composantes distinctes.

**Réduction R (prouvée).** Conjecture 199 ⇐ [L+] ∧ [Couche], où
- **L+** : tout G connexe avec α ≥ κ + 3 a t ≥ κ + 3 (énoncé sans hamiltonicité) ;
- **Couche** : si κ ≥ 2, α = κ + 2, G non traçable, alors pour (au moins un) plus long chemin P et une composante H, G − N(H) a κ + 2 composantes.
Preuve : G non traçable ⇒ α ≥ κ + 2 [CE-chemin]. κ = 1 : T1. α ≥ κ + 3 : L+. α = κ + 2 : Couche + T4 (|X| = κ) + L3. ∎
Remarques : Couche est fausse pour κ = 1 (filet : P = a′acbb′, X = {c}, a′ et b reliés par ab) et son analogue « cycle » est faux (Petersen : G − N(u) contient un C6 connexe) ⇒ une preuve doit utiliser κ ≥ 2 et les extrémités du chemin.

**Version faible (réduite à L′).** L′ : t ≥ min(α, κ + 2) pour tout G connexe. L′ ⇒ « t − 1 ≤ κ ⇒ traçable » (t ≤ κ+1 ⇒ α ≤ κ+1 ⇒ [CE-chemin]). L′ prouvé pour κ ≤ 2 (L4 : α ≥ 3 ⇒ t ≥ 4) ; ouvert pour κ ≥ 3.
L′ ∧ L+ ⟺ **Lemme T : t ≥ min(α, κ + 3)** ; prouvé pour κ = 1 (L4) ; la constante 3 est optimale (couronne K_m∘K_1 : α = m, κ = 1, t = 4).
Premier cas ouvert de L+ : G 2-connexe, α ≥ 5 ⇒ arbre induit à 5 sommets (P5, chaise ou K_{1,4}) — analyse de cas finie amorcée (si v a 3 voisins a1,a2,a3 dans A et w ~ v, w ~ a4, alors w est adjacent à exactement 2 des ai, sinon chaise), non terminée.

## 4. Tests (tous graphes connexes, nauty-geng)
| Énoncé | Résultat |
|---|---|
| L (α ≥ κ+2 ⇒ t ≥ κ+3) | **faux** : F?z\w (n=7 : triangle 456, 0~456, 1~45, 2~46, 3~56 ; κ=2, α=4, t=4, traçable) ; 7 graphes n=8 |
| L′ : t ≥ min(α, κ+2) | vrai n ≤ 10 (11 716 571 graphes n=10) |
| t ≥ min(α+1, κ+2) | faux (G?z\z{ n=8 ; 6 graphes n=9) |
| L+ : α ≥ κ+3 ⇒ t ≥ κ+3 | vrai n ≤ 10 (11 716 571 graphes n=10) |
| Couche (tout (P,H), κ≥2, α=κ+2, non traçable) | vrai n ≤ 10 (n=10 : 587 graphes, 618 096 chemins orientés ; n=9 : 130) |
| S1 : arbre induit contenant |A|−1 sommets de A (|A| ≤ κ+2) | faux : G?otYw (n=8) |
| Variantes enracinées (a ∈ A feuille d'un arbre d'ordre ≥ |A|) | vraies n ≤ 9, **fausses n=10** (4 et 979 cas) |
| Borne en |N(H)| au lieu de κ (t ≥ |N(H)|+3) | faux pour tout (P,H) : G?`Drk (n=8, κ=1, t=4) |
| Arbre dans H ∪ X ∪ X± ∪ {v1,vm} d'ordre ≥ κ+3 | faux pour 84 couples (P,H) n=8, et pour tout (P,H) sur 3 graphes (κ=1) |
| κ ≥ 2 non traçable ⇒ K_{1,κ+2} induit | vrai n ≤ 9 ; 20 exceptions n=10 (κ=2, t ∈ {6,7,8}) ; faux en général : L(S′(Petersen)) (45 sommets, sans griffe, κ=2, non traçable : Petersen a 10 sommets impairs, pas de trail dominant) |
| Couche, variante « ∃ séparateur minimum à κ+2 composantes » | vrai n ≤ 10 (587 graphes n=10, δ ≥ 2) |

Marge t − κ des non traçables (n=8) : 3:29, 4:234, 5:515, 6:287, 7:22 ; jamais < 3 (marge de la conjecture = −1 au mieux).
Familles extrémales (non traçables, t = κ + 3) : K_κ ∨ \bar K_{κ+2} (étoile, tout κ), filet (κ=1, P4), multipartis complets avec 2α = n + 2. Pour κ ≥ 2 et n ≤ 9, tous les cas serrés sont des étoiles K_{1,κ+2}.

## 5. Trous (honnêteté)
- L+ (et donc Lemme T) non prouvé pour κ ≥ 2 ; aucune preuve trouvée par arbre maximal / éventail de Menger (S1 et variantes enracinées réfutées).
- Couche non prouvée pour κ ≥ 2 : seuls P1–P8 sont établis ; il manque « pas de chemin dans G − X entre deux segments de P − X ».
- T3 repose sur [B], [ŁP], [KV] (non vérifiés ici, références confirmées par recherche).
- Vérifications numériques limitées à n ≤ 10.

## 6. Lean (estimation)
- L1, L2, L3, L5, T2 : élémentaire, ~500–900 lignes (dont « Δ ≤ 2 connexe ⇒ chemin/cycle ⇒ chemin hamiltonien » ~300).
- L4 : ~150 lignes. T1 et la réduction R : exigent [CE] (absent de Mathlib) ~1500–3000 lignes.
- T3 : hors de portée (théorèmes profonds).

## 7. Feuilles de l'arbre de réduction (message coordinateur)
Feuilles visées : `R1.H2.R1.H2.R1.H1` (sans triangle, non biparti, C5, κ ≥ 3, α ≥ κ+2, Gᶜ connexe, c(G−U) ≤ |U|+1) et `.R1.H2` (avec triangle).
**Aucune des deux n'est prouvée.**
- H1, tests : aucun graphe sans triangle non biparti ne satisfait κ ≥ 3, α ≥ κ+2, t ≤ κ+2 pour κ = 3 et n ≤ 13 (geng -ct -d3 -D4, 39 449 candidats n=13), ni pour κ = 4 et n ≤ 13 (geng -ct -d4 -D5). Les seuls survivants sont 4 graphes **bipartis** (n=12, κ=4). ⇒ H1 semble **vide** (hypothèses contradictoires) : viser une preuve par contradiction, sans utiliser la traçabilité ni Gᶜ connexe ni la condition de dispersion.
  (Filtre justifié : sans triangle ⇒ N(v) indépendant ⇒ t ≥ Δ + 1 ⇒ Δ ≤ κ + 1 ≤ δ + 1.)
- H1, lemmes prouvés (sans triangle, t ≤ κ+2) : (i) Δ ≤ κ+1 ; (ii) **attache** : pour tout x, si S(x) = {z ∉ N[x] : |N(z) ∩ N(x)| = 1}, alors N[x] ∪ I est un arbre induit pour tout I ⊆ S(x) indépendant ; donc d(x) = κ+1 ⇒ S(x) = ∅, et d(x) = κ ⇒ S(x) est une clique, |S(x)| ≤ 2 ; (iii) tout C5 est induit. Il manque l'argument qui combine le C5 et α ≥ κ+2 (analogue non biparti de `all_rows_overlap` : pour u, v à distance 2, l'arbre {u, z, v} ∪ (indépendant du graphe de conflit biparti entre N(u)∖N(v) et N(v)∖N(u)) a 3 + α(M_uv) sommets, d'où α(M_uv) ≤ κ − 1 ; dans le cas biparti M_uv est vide, ici les arêtes de M_uv sont exactement les C5 passant par u–z–v).
- H2 (triangle) : non abordée faute de budget.

## Manche 2 — feuille R1.H2.R1.H2.R1.H1 (sans triangle, non biparti, C5, κ ≥ 3, α ≥ κ+2, t ≤ κ+2)
Verdict : **vacuité NON prouvée** ; trou exact ci-dessous. Notation k = κ(G), G sans triangle, t ≤ k+2.

Lemmes prouvés (élémentaires ; arbres induits explicites) :
- M1 (étoile). N(v) indépendant ⇒ étoile N[v] ⇒ Δ ≤ k+1 ; δ ≥ k (F1). Degrés ∈ {k, k+1}.
- M2 (arête, piste b). Pour uv ∈ E, U = N(u)−v, W = N(v)−u sont disjoints et indépendants ; tout indépendant I de B(uv) = G[U ∪ W] donne l'arbre {u,v} ∪ I ⇒ α(B(uv)) ≤ k ⇒ (König) ν(B(uv)) ≥ d(u)+d(v)−2−k ≥ k−2 ≥ 1 : toute arête est dans ≥ k−2 C4 à paires disjointes. Corollaire : au plus k+1−d(u) sommets de W sans voisin dans U.
- M3 (attache, piste c). S(x) = {z ∉ N[x] : |N(z) ∩ N(x)| = 1}. Pour I ⊆ S(x) indépendant, N[x] ∪ I est un arbre ⇒ d(x) = k+1 ⇒ S(x) = ∅ ; d(x) = k ⇒ S(x) clique, |S(x)| ≤ 2.
- M4 (distance 2). u ≁ v, z voisin commun : {u,z,v} ∪ I (I indépendant de G[N(u) Δ N(v)]) est un arbre ⇒ α(G[N(u) Δ N(v)]) ≤ k−1. Si N(u) ∪ N(v) est indépendant, |N(u) Δ N(v)| ≤ k−1 (= `private_neighbors_bound`) ; les arêtes de N(u) Δ N(v) sont exactement les C5 u–z–v–y–x.
- M5 (indépendant + arête interne). A indépendant maximal, B = V∖A, p(b) = |N_A(b)| ≥ 1. Pour xy ∈ E(G[B]) : N_A(x) ∩ N_A(y) = ∅ et {x,y} ∪ N_A(x) ∪ N_A(y) est une double étoile ⇒ p(x)+p(y) ≤ k ; donc deg_B(x) ≥ k − p(x). Avec M2 : N_A(y) ⊆ N(N_B(x)−y) sauf ≤ 1 sommet. G non biparti ⇒ G[B] a une arête pour tout A.
- M6 (classes du C5 c0…c4). V_i = N(c_{i−1}) ∩ N(c_{i+1}) : c_i ∈ V_i, les V_i sont disjoints, indépendants, V_i et V_{i+2} sans arête (voisin commun c_{i+1}) ; double étoile sur c_i c_{i+1} avec feuilles V_{i−1}, V_{i+2} ⇒ |V_{i−1}| + |V_{i+2}| ≤ k, Σ|V_i| ≤ 5k/2.
- Piste d (« deux sommets non adjacents du C5 ont des voisinages disjoints ») : **fausse** (c0, c2 partagent c1 ; dans C5[a] toute la classe 1).
- Les V_i ne couvrent pas V en général (And(4) : V_i = {c_i}), donc M6 ne donne pas de structure globale.

Tests (geng -ct, n ≤ 15) :
- Sans la condition sur α, les seuls graphes sans triangle non bipartis avec κ ≥ 3 et t ≤ κ+2 trouvés sont : C5[2] (n=10, κ=4), Andrásfai And(4) = circulant(11;1,4) (n=11, κ=4), And(5) = circulant(14;1,4,7) (n=14, κ=5), C5[3] (n=15, κ=6), un graphe n=16 (κ=6, 6-régulier ou non, O??EEBo{Fw^_NoNo@}?^_). Tous : α = κ ; diamètre 2 et « indépendants maximaux = voisinages » vérifiés seulement pour les quatre premiers (familles connues), pas pour celui à n=16.
- Avec α ≥ κ+2 : **aucun** (κ=3 : n ≤ 13 ; κ=4 : n ≤ 15 ; κ ∈ {5,6} avec δ ≥ 5, Δ ≤ 6 : n ≤ 16). 4 survivants bipartis à n=12 (κ=4).
- Version locale (δ à la place de κ, sans connexité) : aucun survivant pour δ ∈ {3,4}, n ≤ 13 ; fausse si non connexe (2·C5[2], n=20).

**Trou exact (lemme G)** : G sans triangle, non biparti, κ = k ≥ 3, t ≤ k+2 ⇒ α ≤ k+1 (contredit α ≥ k+2). Les données suggèrent plus fort : G est un éclatement (blow-up) d'un graphe d'Andrásfai, donc α = Δ ≤ k+1. Voie proposée : montrer que tout indépendant maximal est contenu dans un voisinage (vrai sur tous les survivants), via M3/M5 appliqués à un indépendant maximum A et une arête de G[V∖A].
Lean : M1–M6 ≈ 400–700 lignes (réutilisent `star_bound`, `private_neighbors_bound`, `connector_tree_of_common_component`) ; lemme G : non estimable (pas de preuve).

## Manche 3 — lemme G (sans triangle, non biparti, κ = k ≥ 3, t ≤ k+2 ⇒ α ≤ k+1)
Verdict : **G non prouvé**. Réduction partielle nouvelle, assistée par ordinateur (cas fini), pour k ≤ 5.
Notation : A indépendant maximal, B = V∖A, S_b = N_A(b), s_b = |S_b| ≥ 1 ; B₁ = sommets de B ayant un voisin dans B (B₁ ≠ ∅ car G non biparti).

Lemmes prouvés (en plus de M1–M6) :
- M7 (piste i, généralisée). Si X ⊆ B est indépendant et si le graphe d'incidence entre X et ⋃_{x∈X} S_x est un arbre, alors G[X ∪ ⋃S_x] est cet arbre ⇒ |X| + |⋃S_x| ≤ k+2. Cas |X| = 2, |S_b ∩ S_c| = 1 : s_b + s_c ≤ k+1 (piste i d'Opus, correcte). Variante « voisins privés » : b ≁ c, S_b ∩ S_c ∋ a ⇒ l'arbre {b,a,c} ∪ (S_b Δ S_c) donne |S_b Δ S_c| ≤ k−1 (valable sans hypothèse biparti car A est indépendant).
- M8 (araignée, piste iii). y ∈ B₁, s = s_y, q = k − s (q ≥ 1 car un voisin x ∈ N_B(y) a s_x ≥ 1 et s + s_x ≤ k par M5). Lignes R_x = S_x (x ∈ N_B(y)) : r = |N_B(y)| ∈ {q, q+1} (M1), |R_x| ≤ q (M5), R_x ∩ S_y = ∅, et pour toute sous-famille non vide X ⊆ N_B(y), l'arbre {y} ∪ S_y ∪ X ∪ once(X) donne |X| + once(X) ≤ q+1, où once(X) = sommets de A couverts exactement une fois par X. ⋃R_x = A ∩ D₂(y) (A à distance exactement 2 de y).
- C2* (combinatoire finie, vérifiée exhaustivement, `r199/c2star.c`). Énoncé : aucune famille (multi-ensemble, lignes vides permises) de r ∈ {q, q+1} parties d'un ensemble de q+2 points, de tailles ≤ q, de réunion totale, avec |X| + once(X) ≤ q+1 pour toute sous-famille X. **Vrai pour q ≤ 4** (q=4 : 8 435 nœuds) ; **faux pour q ≥ 5** (q=5 : lignes {0,1,2,3}², {0,1,4,5}², {0,2,4,6} ; q=6 : idem, plan de Fano).
  Réduction à |U| = q+2 : supprimer un point de toutes les lignes ne fait pas croître |X| + once(X).
- **Lemme L (prouvé pour k ≤ 5, via M8 + C2*)** : pour tout y ∈ B₁, |A ∩ N_{≤2}[y]| = s_y + |A ∩ D₂(y)| ≤ k+1 (q = k − s_y ≤ k − 1 ≤ 4).
- **Corollaire** : pour k ∈ {3,4,5}, le lemme G ⇐ (D) : « il existe y ∈ B₁ tel que A ⊆ N_{≤2}[y] », en particulier ⇐ (G1) : diam(G) = 2.

Tests :
- Les 6 graphes de la classe (sans triangle, non biparti, κ ≥ 3, t ≤ κ+2) trouvés pour n ≤ 16 sont And(3) (n=8, κ=3, trouvé au test G2 ; il avait échappé à la Manche 2, partie de n = 10), C5[2], And(4), And(5), C5[3] et le graphe n=16. Tous ont α = κ. Le diamètre 2 est vérifié pour C5[2], And(4), And(5), C5[3] ; non vérifié pour And(3) ni pour le graphe n=16.
- G2 (sans triangle, diamètre 2, δ ≥ k ≥ 3, Δ ≤ k+1, t ≤ k+2 ⇒ α ≤ k+1, biparti autorisé) : vrai pour n ≤ 14 (29 123 001 graphes n=14) ; membres de la classe : K_{p,p}, K_{p,p+1}, And(s), C5[a].

Trous exacts : (1) (D) ou G1 (diamètre 2) — aucune preuve ; c'est le point où la non-bipartition doit servir (les survivants bipartis ont des paires à distance 3). (2) Pour k ≥ 6, C2* est faux : il faut des contraintes non locales (arbres passant par N_B(x), degrés des sommets de A).
Lean : M7–M8 ≈ 300 lignes ; C2* pour q ≤ 4 par `decide` sur un énoncé fini (taille ≈ 2^6 masques, faisable mais lourd) ; le reste n'est pas estimable.

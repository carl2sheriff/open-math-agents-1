# Vérification indépendante — WOWII 189, Théorèmes D, D⁺, D⁺⁺ (relecteur D)

Texte relu : `research-189.md` §0, §2, §3 (Thm C, dépendance de D), §4 (R4, R6), « Étape H2 » (H2.1–H2.5), « Étape H2 — Manche 2 » (M2.1, M2.2, M2.7). Définitions Lean contrôlées : `secondSmallestDegree = (degreeSequence G).getD 1 0` (suite triée, doublons compris) ⇒ Fait 0 correct ; `distEven` compte v lui-même ⇒ (H) ⇔ |Γ(v)| ≤ σ.
Tests numériques : `wowii/verifD/struct.py` (structure pure, sans (H)) : tous les graphes connexes non traçables n = 5..8 (1 230 graphes, 337 192 chemins x₀-plus longs, tous les choix de x₀) + `h2m2/nt10s.g6` (250 graphes, 388 644 chemins) : Lemme 4, 5a, 5b, P(a), N_P(y)^± ⊆ L₂(y), |N_P(y)^±| = c+1+g, (Q1)(i)(ii) (toutes paires d'attaches), (E) (toutes attaches a) : **0 échec**.

## §0, §2, §4
| Item | Verdict | Remarque |
|---|---|---|
| §0 notations, Fait 0, σ ≥ 1 | VALIDE | |
| Lemme 1, Cor. 1a, 1b | VALIDE | somme = (n−|S|) + 2|S_p| |
| Lemme 2, Cor. 2a | VALIDE | d₂ atteint par un sommet ≠ x₀ |
| Lemme 3 | VALIDE | |
| Lemme 4 (+ version x₀) | VALIDE | testé |
| Lemme 5a, 5b | VALIDE | testé |
| Lemme 5c | VALIDE | les k+1 indices j₁−1, j₁+1, …, j_k+1 sont distincts |
| Lemme 6a, 6b | VALIDE | |
| Thm C (dépendance) | VALIDE | |
| (R4) (global et x₀-plus long) | VALIDE | le point délicat (w ∈ F(x₁) ∩ V(P) sans voisin dans R) est bien couvert par A3 |
| (R6) | VALIDE | |

## Étape H2
| Item | Verdict | Remarque |
|---|---|---|
| H2.1 cadre x₀-plus long, rotation, m ≥ 2σ+2 | VALIDE | |
| Lemme P (a) | VALIDE | testé |
| **Lemme P (b) / (Q2) / (c)** | **ERREUR (locale, réparable)** | voir E1 |
| Corollaire (singleton, P₃) | VALIDE | n'utilise pas B_y |
| E′ (arête) | VALIDE | K = {y,z} : B_y correct ; cas c ≥ 3 / c = 2 (trou = x₀ : x₀ ≁ x_{j−1}, x_{j+3}) / c = 1 vérifiés |
| **Théorème D (n ≤ 2σ+4)** | **VALIDE** | Thm C + Cor. 1b + (R4) + 5c + E′ |
| H2.4 « Conséquence n = 2σ+5 » | VALIDE (remplacé par D⁺) | |
| H2.5 (F1)–(F3), (G) | VALIDE | hors chaîne de D ; (F2) via (F1), (F3) via (F1), (G) : chemin hamiltonien correct (j' ≥ j+2) |

### E1 — Lemme P(b) : B_y mal défini
B_y := N_P(K \ {y}) \ N_P(y). L'affirmation « B_y à distance exactement 2 de y » n'est vraie que pour les attaches des **voisins** de y dans K. Un sommet x ~ u avec u ∈ K non adjacent à y peut être à distance 3.
Contre-exemple structurel (vérifié par `struct.py`) : P = x₁…x₁₁, K = chemin y–a–u, y ~ x₄, u ~ x₈, x₀ = x₆ (g6 `MhCGGC@?G?a??@?O_`). P est le plus long chemin contenant x₀ (et même le plus long chemin), B_y = {x₈}, d(y, x₈) = 3 ∉ Γ(y).
**Correction** : B'_y := N_P(N_K(y)) \ N_P(y). Avec B'_y, (b), (c) et (Q2) sont vrais (0 échec sur les tests ci-dessus). B_y = B'_y quand y est adjacent à tout K \ {y}, donc **E′, (Q4), K₃, K₄ ne sont pas touchés**. Seuls touchés : C₄ et diamant (M2.7 cas A), plus l'énoncé général de (Q2) cité en M2.5.

## Manche 2
| Item | Verdict | Remarque |
|---|---|---|
| (Q1) régions | VALIDE | testé (toutes paires d'attaches, pas seulement consécutives) |
| (Q2) | ERREUR → VALIDE avec B'_y | E1 |
| (Q3) | VALIDE | k = 1 ⇒ K₂ = ∅ ne dépend pas de B ; k = 0 exclu par 5c |
| (Q4) K₃ ⇒ σ ≤ 5 | VALIDE | cas « tous |B_y| = 1 » : un écart de pas 2 de y est un écart de A (sinon x_{i+1} ∈ A contredit (Q1ii)), donc il contient x₀ |
| **Théorème D⁺ (n = 2σ+5)** | **VALIDE** | réduction à R = K₃, m = 2σ+2 ; σ = 2, 3, ≥ 5 par m ≥ 4r+1 ; σ = 4 : (a) q = p+2 ; (b) gauche p=3, q=7 (x₁ ~ x₅ forcé ⇒ 12 sommets) ; milieu x₀ = x₅ (x₅ ≁ x₃ ; x₅ ~ x₇ ⇒ x₅ ≁ x₈ sinon hamiltonien) : tous les chemins vérifiés à la main |
| (E), (C) | VALIDE | (E) vaut pour toute attache a < j (pas seulement a₁) ; « retirer A » : légitime seulement si x₁ ∉ N_P(u)^±, vérifié dans chaque cas |

### Théorème D⁺⁺ (n = 2σ+6), M2.7
**Cas B (R = K₃, m = 2σ+3)** — VALIDE.
- σ ≥ 6 (Q4), σ = 2 (m ≥ 8), σ = 3 (égalité 4r+1 = 9 ⇒ x₀ seul au milieu ⇒ |Γ(x₀)| ≥ 5) : OK.
- σ = 5 : régions (3,1,3,3), A = {x₄, x₆, x₁₀}, x₀ = x₅. Γ(u) = {x₃,x₅,x₇,x₉,x₁₁} est exact (c+1+g = 3+1+1). J'ai recalculé N(x₁) = {x₂,x₃,x₈,x₉,x₁₂} et N(x₁₃) = {x₂,x₇,x₈,x₁₁,x₁₂}, d'où le croisement en i = 2 : OK.
- σ = 4 : les cas (régions) sont complets ; (5,8) au milieu = miroir de (4,7), non écrit mais couvert par symétrie. J'ai recalculé chaque ensemble (C) et refait chaque chemin (hamiltonien ou plus long) : OK.
  Les ensembles « forcés » des auteurs n'emploient (E) qu'en a₁. Avec (E) aussi en a_r, on conclut parfois plus vite : (4,8) x₀ = x₆ donne N(x₁) ⊆ {x₂,x₃,x₇}. Leur raisonnement reste valide.

**Cas A, K₄** — VALIDE, avec un TROU mineur.
- m ≥ 5r−2 : correct (au plus un écart non croisé).
- σ = 6 (tout y voit A ⇒ m ≥ 16) : OK. σ = 5 : sous-cas (3,8) et (5,8) vérifiés, y compris l'exactitude de Γ(u) = {x₁,x₂,x₄,x₇,x₉}.
- TROU mineur, σ = 4 : « deux régions ≥ 4 » suppose que l'écart médian est croisé. Il faut le justifier : si x_p et x_q étaient privés d'un seul y, les trois autres sommets auraient c = 0 < σ−3 = 1. Réparation immédiate.

**Cas A, C₄** — conclusion VALIDE, justification fautive (E1). Avec B' : B'_z = ∅ donne N_P(a) ∪ N_P(b) ⊆ N_P(z), et B'_a = ∅ donne N_P(z) ∪ N_P(z') ⊆ N_P(a). Les 4 sommets ont donc la même trace A, en progression de pas 2. La suite du texte est alors correcte : σ ≥ 5 ✗, σ = 4 donne m ≥ 11 > 10, σ = 3 donne r = 1 contre (R6), σ = 2 donne m ≥ 9.

**Cas A, diamant** (z, z' de degré 2 dans K ; a, b de degré 3) — **ERREUR de rédaction, conclusion réparable.**
Avec B' seulement, on a N_P(a) ∪ N_P(b) ⊆ N_P(z) ∩ N_P(z'). En revanche N_P(z) = N_P(z') n'est pas établi. L'étape « N_P = A pour ces sommets » et l'argument σ = 3 ⇒ r = 1 ne sont donc pas justifiés : z ~ x_p, z' ~ x_q avec p ≠ q, et a, b sans attache, est compatible avec (Q2) corrigé.
Réparation (vérifiée) :
1. Pour un écart (x_i, x_{i+2}) de z avec x_{i+1} ≠ x₀, x_i et x_{i+2} sont **privés** de z. Si a, b ou z' voit l'un d'eux, on remplace x_{i+1} par un chemin hamiltonien du diamant (z–b–z'–a, etc.) : m+3 sommets.
2. σ ≥ 5 : z a ≥ 2 écarts, dont au plus un contient x₀. Donc au plus une attache de z est non privée, d'où c(a) ≤ 1 < σ−3. Contradiction.
3. σ = 4 : la seule attache non privée possible impose x₀ = x_{p+1} pour z et pour z'. Donc N_P(z) = N_P(z') = A = {x_p, x_{p+2}}, et (Q1i) avec h = 4 donne m ≥ 11 > 10.
4. σ = 3 : soit N_P(z) = N_P(z') (r = 1, contre (R6)), soit A = {x_p, x_q} avec p < q. Dans ce second cas, (Q1i/ii) avec le chemin z–a–b–z' (h = 4) donne deux régions sans x₀ de taille ≥ 4, d'où m ≥ 11 > 8.
5. σ = 2 : comme dans le texte.

**Verdict D⁺⁺ : VALIDE après réparation** (E1 + diamant + trou mineur K₄ σ = 4). La conclusion n = 2σ+6 ⇒ traçable tient. Le texte doit corriger la définition de B_y dans le Lemme P et (Q2), et réécrire le cas diamant.

## Synthèse
- D : VALIDE.
- D⁺ : VALIDE.
- D⁺⁺ : VALIDE après réparation.
- Erreur trouvée : définition de B_y (Lemme P(b), (Q2)), fausse dès que K n'est pas une clique (contre-exemple n = 14). Elle fait tomber la justification des cas C₄ et diamant de M2.7. Le cas C₄ est sauvé directement ; le cas diamant demande la réparation ci-dessus.
- Pour M2.5 : utiliser (Q2) avec B'_y pour les cas suivants (n ≥ 2σ+7).

# WOWII 40 / 189 / 199 : recherche de contre-exemples (resultat : AUCUN)
Scripts : sweep.c (balayage C, invariants comme en Lean), verify.py (reimplementation independante networkx, force brute, accord exact sur n<=7),
families.py (hill-climb clique+independant, n<=30), fam14.py (familles n<=14 passees dans sweep).
- Conj 40 : aucun contre-exemple, tous graphes connexes n=2..10 (11 716 571 graphes au total n=2..10 verifies, n=10 : 11 716 571 graphes). Egalites frequentes (K_n, etoiles K_{1,m}, K_{a,b} ex. K_{3,3}, K_{2,5}) : borne serree.
- Conj 189 : aucun contre-exemple, tous graphes connexes n=2..11 (n=11 : 1 006 700 565 graphes, compte conforme).
- Conj 199 : aucun contre-exemple, tous graphes connexes n=2..10.
- Familles : 6477 graphes n<=14 (K_{a,b}, K_a v indep, coronas, Petersen, arbres aleatoires, split aleatoires) : 0 CE pour les trois. Hill-climb clique K_m + independant t>=m+2 (non-hamiltonien par coupe), n<=30 : meilleure marge -1 pour 189 et 199 (jamais >=0).
Limites : 40 et 199 non balayes a n=11 ; familles n 15..30 couvertes uniquement par le hill-climb split (pas de coronas/Petersen generalises).

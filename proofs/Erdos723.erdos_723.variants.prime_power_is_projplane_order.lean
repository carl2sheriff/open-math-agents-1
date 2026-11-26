import FormalConjectures.ErdosProblems.«723»

open Configuration

theorem OMA.solution : type_of% @Erdos723.erdos_723.variants.prime_power_is_projplane_order := by
  intro n hn
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
  haveI : Fact p.Prime := ⟨hp⟩
  letI : DecidableEq (GaloisField p k) := Classical.decEq _
  haveI : NeZero k := ⟨hk.ne'⟩
  have hq : Nat.card (GaloisField p k) = p ^ k := by
    exact GaloisField.card p k hk.ne'
  have hq1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
  haveI : Finite (Projectivization (GaloisField p k) (Fin 3 → GaloisField p k)) :=
    Projectivization.finite_of_finite _ _
  letI : Fintype (Projectivization (GaloisField p k) (Fin 3 → GaloisField p k)) :=
    Fintype.ofFinite _
  refine ⟨Projectivization (GaloisField p k) (Fin 3 → GaloisField p k),
    Projectivization (GaloisField p k) (Fin 3 → GaloisField p k), inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  set q := p ^ k with hqdef
  have h1 := Projectivization.card' (GaloisField p k) (Fin 3 → GaloisField p k)
  have hV : Nat.card (Fin 3 → GaloisField p k) = q ^ 3 := by
    rw [Nat.card_fun, hq]; simp
  rw [hV, hq] at h1
  have h2 := ProjectivePlane.card_points
    (P := Projectivization (GaloisField p k) (Fin 3 → GaloisField p k))
    (L := Projectivization (GaloisField p k) (Fin 3 → GaloisField p k))
  rw [Fintype.card_eq_nat_card] at h2
  set o := ProjectivePlane.order (Projectivization (GaloisField p k) (Fin 3 → GaloisField p k))
    (Projectivization (GaloisField p k) (Fin 3 → GaloisField p k))
  set N := Nat.card (Projectivization (GaloisField p k) (Fin 3 → GaloisField p k))
  obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hN : N = q ^ 2 + q + 1 := by
    have h3 : q ^ 3 = N * r + 1 := by
      rw [h1]; congr 2; omega
    have hr0 : 0 < r := by omega
    have : r * N = r * (q ^ 2 + q + 1) := by
      rw [hr]; rw [hr] at h3; nlinarith [h3]
    exact Nat.eq_of_mul_eq_mul_left hr0 this
  rw [hN] at h2
  have : o ^ 2 + o = q ^ 2 + q := by omega
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · nlinarith
  · nlinarith

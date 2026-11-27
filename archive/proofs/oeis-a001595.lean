import OMAStatements.S_oeis_a001595

theorem OMA.solution : type_of% @OMA.S_oeis_a001595.main := by
  have h1 : PowerSeries.mk OMA.S_oeis_a001595.a *
      (1 - 2 * (PowerSeries.X : PowerSeries ℤ) + PowerSeries.X ^ 3) =
      1 - PowerSeries.X + PowerSeries.X ^ 2 := by
    ext n
    have e : PowerSeries.mk OMA.S_oeis_a001595.a *
        (1 - 2 * (PowerSeries.X : PowerSeries ℤ) + PowerSeries.X ^ 3) =
        PowerSeries.mk OMA.S_oeis_a001595.a - 2 * (PowerSeries.X ^ 1 * PowerSeries.mk OMA.S_oeis_a001595.a)
          + PowerSeries.X ^ 3 * PowerSeries.mk OMA.S_oeis_a001595.a := by ring
    rw [e]
    simp only [map_add, map_sub, PowerSeries.coeff_mk]
    rw [show (2 : PowerSeries ℤ) * (PowerSeries.X ^ 1 * PowerSeries.mk OMA.S_oeis_a001595.a) =
      PowerSeries.C (2 : ℤ) * (PowerSeries.X ^ 1 * PowerSeries.mk OMA.S_oeis_a001595.a) by simp,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
    rcases n with _ | _ | _ | n
    · simp [OMA.S_oeis_a001595.a]
    · simp [OMA.S_oeis_a001595.a, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    · simp [OMA.S_oeis_a001595.a, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    · simp [PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      simp only [OMA.S_oeis_a001595.a]
      ring
  refine ⟨h1, ?_⟩
  have e1 : (1 - (PowerSeries.X : PowerSeries ℤ) - PowerSeries.X ^ 2) * (1 - PowerSeries.X) =
      1 - 2 * PowerSeries.X + PowerSeries.X ^ 3 := by ring
  have e2 : 2 * (1 - (PowerSeries.X : PowerSeries ℤ)) - (1 - PowerSeries.X - PowerSeries.X ^ 2) =
      1 - PowerSeries.X + PowerSeries.X ^ 2 := by ring
  rw [e1, e2]; exact h1

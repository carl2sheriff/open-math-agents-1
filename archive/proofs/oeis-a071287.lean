import OMAStatements.S_oeis_a071287

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071287.main) := by
  intro h
  have := h.2 6
  revert this
  decide

import OMAStatements.S_oeis_a071283

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071283.main) := by
  intro h
  have := h.2 4
  revert this
  decide

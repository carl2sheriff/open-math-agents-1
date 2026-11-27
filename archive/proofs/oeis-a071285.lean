import OMAStatements.S_oeis_a071285

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071285.main) := by
  intro h
  have := h.2 5
  revert this
  decide

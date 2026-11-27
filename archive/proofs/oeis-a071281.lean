import OMAStatements.S_oeis_a071281

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071281.main) := by
  intro h
  have := h.2 3
  revert this
  decide

namespace tactic
  open well_founded_tactics

  /-- `fst_dec_tac`, but without the `abstract` (and thus zeta reducing). -/
  meta def fst_dec_tac' : tactic unit := do
      clear_internals,
      unfold_wf_rel,
      process_lex (unfold_sizeof >> try (tactic.dunfold_target [``psigma.fst])
                >> cancel_nat_add_lt >> trivial_nat_lt)

  /-- An alternative version of `dec_tac` which also unfolds .fst indexing.

      This is required for the various proofs which skip the implicit context
      argument. -/
  meta def fst_dec_tac : tactic unit := abstract fst_dec_tac'

end tactic

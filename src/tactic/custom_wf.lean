namespace tactic
  open tactic
  open well_founded_tactics

  /-- An alternative version of dec_tac which also unfolds .fst indexing.

      This is required for the various proofs which skip the implicit context
      argument. -/
  meta def fst_dec_tac : tactic unit := abstract $ do
      clear_internals,
      unfold_wf_rel,
      process_lex (unfold_sizeof >> try (tactic.dunfold_target [``psigma.fst])
                >> cancel_nat_add_lt >> trivial_nat_lt)
end tactic

open tactic interactive interactive.types lean.parser expr

private meta def set_cases_tags (in_tag : tag) (rs : list name) : tactic unit := do
  te ← tags_enabled,
  gs ← get_goals,
  match gs with
  | [g] := when te (set_tag g in_tag) -- if only one goal was produced, we should not make the tag longer
  | _   := do
    let tgs : list (name × expr) := rs.map₂ (λ n g, (n, g)) gs,
    if te
    then tgs.mmap' (λ ⟨n, g⟩, set_tag g (n::in_tag))
        /- If `induction/cases` is not in a `with_cases` block, we still set tags using `_case_simple` to make
            sure we can use the `case` notation.
            ```
            induction h,
            case c { ... }
            ```
        -/
    else tgs.mmap' (λ ⟨n, g⟩, with_enable_tags
      (set_tag g (name.mk_numeral (unsigned.of_nat 0) `_case::n::[])))
  end

meta def known_induction (ty : parse ident) (gen : parse texpr) : tactic unit := do
  in_tag ← get_main_tag,
  focus1 $ do {
    gen <- i_to_expr gen,

    env ← tactic_state.env <$> read,
    ty ← resolve_constant ty
          <|> fail ("'" ++ to_string ty ++ "' cannot be found"),
    let ctors := environment.constructors_of env ty,

    rw ← apply gen,
    set_cases_tags in_tag ctors
  }

run_cmd add_interactive [`known_induction]

example : ∀ (n : ℕ), 0 < (nat.succ n) := λ n, begin
  known_induction nat (@nat.rec_on (λ n, 0 < (nat.succ n)) n),
  case nat.zero { from nat.zero_lt_succ _ },
  case nat.succ : n ih { from nat.zero_lt_succ _ },
end

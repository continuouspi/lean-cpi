import tactic.lint

run_cmd lint
set_option profiler true
set_option profiler.threshold 0.5

/-- A dependently typed and. Equivalent to Σ', but on the property level. -/
structure pand {α : Prop} (β : α → Prop) : Prop :=
  mk :: (fst : α) (snd : β fst)

notation `Σ∧` binders `, ` r:(scoped p, pand p) := r

#lint

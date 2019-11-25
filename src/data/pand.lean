import tactic.lint

/-- A dependently typed and. Equivalent to Σ', but on the property level. -/
structure pand {α : Prop} (β : α → Prop) : Prop :=
  mk :: (fst : α) (snd : β fst)

notation `Σ∧` binders `, ` r:(scoped p, pand p) := r

#lint -

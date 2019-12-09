import logic.embedding

universes u v

/-- An embedding which distributes over an operator. -/
structure distrib_embedding (α : Sort u) (β : Sort v) (opl : α → α → α) (opr : β → β → β) :=
  (to_embed : α ↪ β)
  (distrib : ∀ x y, to_embed (opl x y) = opr (to_embed x) (to_embed y))

instance {α : Sort u} {β : Sort v} (opl : α → α → α) (opr : β → β → β)
  : has_coe_to_fun (distrib_embedding α β opl opr)
  := { F := _, coe := λ x, x.to_embed.to_fun }

instance {α : Sort u} {β : Sort v} (opl : α → α → α) (opr : β → β → β)
  : has_coe (distrib_embedding α β opl opr) (α ↪ β)
  := { coe := λ x, x.to_embed }

/-- A distrib_embedding which embeds to the same type (equivalent to the
    identity function). -/
@[refl] def distrib_embedding.refl {α : Sort u} (op : α → α → α) : distrib_embedding α α op op
  := { to_embed := function.embedding.refl α,
       distrib := λ x y, rfl }

#lint-

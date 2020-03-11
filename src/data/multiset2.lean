import data.fintype algebra.big_operators

/-- finset.sum_bij, but on isomorphism. -/
lemma finset.sum_iso {α₁ α₂ β: Type} [add_comm_monoid β]
    (f : α₁ → β) (g : α₂ → β) (iso : α₁ ≃ α₂)
    (feq : ∀ x, f x = g (iso.to_fun x))
    (xs : finset α₁) (ys : finset α₂)
  : (∀ x, x ∈ xs → iso.to_fun x ∈ ys)
  → (∀ y, y ∈ ys → iso.inv_fun y ∈ xs)
  → finset.sum xs f = finset.sum ys g
| mem mem' := finset.sum_bij (λ a _, iso.to_fun a) mem (λ x _, feq x)
    (λ a₁ a₂ _ _ eq, equiv.injective iso eq)
    (λ b mem, ⟨ iso.inv_fun b, mem' b mem, symm (iso.right_inv b) ⟩)

lemma fintype.sum_iso {α₁ α₂ β: Type} [add_comm_monoid β] [xs : fintype α₁] [ys : fintype α₂]
    (f : α₁ → β) (g : α₂ → β) (iso : α₁ ≃ α₂)
    (feq : ∀ x, f x = g (iso.to_fun x))
  : finset.sum (fintype.elems α₁) f = finset.sum (fintype.elems α₂) g
  := finset.sum_iso f g iso feq (fintype.elems α₁) (fintype.elems α₂)
    (λ x _, fintype.complete (iso.to_fun x))
    (λ x _, fintype.complete (iso.inv_fun x))

/-- A composition of filter and image on finsets. -/
def finset.filter_image {α β : Type} [decidable_eq β] (f : α → option β) : finset α → finset β
| ⟨ xs, nodup ⟩ := (multiset.filter_map f xs).to_finset

/-- A composition of filter and map on finsets. This is less elegant a interface
    than finset.map, as f need only be injective over the values it is returns
    'some' for. -/
def finset.filter_map {α β : Type}
  (f : α → option β) (H : ∀ (a a' : α) (b : β), b ∈ f a → b ∈ f a' → a = a') :
  finset α → finset β
| ⟨ xs, nodup ⟩ := ⟨ multiset.filter_map f xs, multiset.nodup_filter_map f H nodup ⟩

#lint -

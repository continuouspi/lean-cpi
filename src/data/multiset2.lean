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

/-- Insert an item into a finset, given a proof it does not occur already. -/
def finset.insert_nmem {α : Type*} : ∀ {xs : finset α} {a : α}, a ∉ xs → finset α
| xs a nmem := ⟨ a :: xs.val, multiset.nodup_cons_of_nodup nmem xs.nodup ⟩

/-- `finset.insert_nmem` with an explicit element and vector, useful for working
    outside of tactic mode. -/
def finset.insert_nmem' {α : Type*} (a : α) (xs : finset α) : a ∉ xs → finset α
  := finset.insert_nmem

lemma finset.mem_insert_nmem_self {α : Type*} {a : α} {s : finset α} (nmem : a ∉ s)
  : a ∈ finset.insert_nmem nmem := multiset.mem_cons_self a s.val

lemma finset.mem_insert_nmem_of_mem {α : Type*} {a b : α} {s : finset α} (h : a ∈ s) (nmem : b ∉ s)
  : a ∈ finset.insert_nmem nmem := multiset.mem_cons_of_mem h

/-- Build a union of two disjoint finite sets -/
def finset.union_disjoint {α : Type*} (xs ys : finset α)
  : multiset.disjoint xs.val ys.val → finset α
| disj := ⟨ xs.val + ys.val, (multiset.nodup_add_of_nodup xs.nodup ys.nodup).mpr disj ⟩

lemma finset.mem_union_disjoint {α : Type*} {a : α} {xs ys : finset α}
    {h : multiset.disjoint xs.val ys.val}
  : a ∈ finset.union_disjoint xs ys h ↔ a ∈ xs ∨ a ∈ ys
  := multiset.mem_add

/-- A composition of `multiset.map` and `multiset.sum`, which has the same
    signature as `finset.sum`. -/
def multiset.sum' {α : Type*} {β : Type*} [add_comm_monoid β] (s : multiset α) (f : α → β) : β
  := (multiset.map f s).sum

@[simp]
lemma multiset.sum'_zero {α : Type*} {β : Type*} [add_comm_monoid β] (f : α → β)
  : multiset.sum' 0 f = 0
  := rfl

@[simp]
lemma multiset.sum'_singleton {α : Type*} {β : Type*} [add_comm_monoid β] (f : α → β) (a : α)
  : multiset.sum' [a] f = f a
  := add_zero (f a)

@[simp]
lemma multiset.sum'_add {α : Type*} {β : Type*} [add_comm_monoid β] (s₁ s₂ : multiset α) (f : α → β)
  : (s₁ + s₂).sum' f = s₁.sum' f + s₂.sum' f
  := by simp only [multiset.sum', multiset.map_add, multiset.sum_add]

#lint-

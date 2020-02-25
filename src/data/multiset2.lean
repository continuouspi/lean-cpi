import data.finset data.list.partition_map

/-- Map elements together and sum them. -/
def multiset.sum_map {α β : Type} [add_comm_monoid β] (f : α → β) (xs : multiset α) : β
  := multiset.fold (+) 0 (multiset.map (λ x, f x) xs)

/-- Applying a map over two finite sets xs ys, where every element of xs
    has a corresponding element in ys, which maps to the same value, results
    in the same sum. -/
lemma finset.map_iso {α₁ α₂ β: Type}
    (f : α₁ → β) (g : α₂ → β) (iso : α₁ ≃ α₂)
    (feq : ∀ x, f x = g (iso.to_fun x))
  : ∀ (xs : finset α₁) (ys : finset α₂)
    , (∀ x, x ∈ xs → iso.to_fun x ∈ ys)
    → (∀ y, y ∈ ys → iso.inv_fun y ∈ xs)
    → multiset.map f xs.val = multiset.map g ys.val
| ⟨ xs, nodupx ⟩ ⟨ ys, nodupy ⟩ efwd erev := begin
  induction xs,
  {
    induction xs generalizing ys,

    case list.nil {
      -- The empty case is trivial: the other item must be an empty set,
      -- otherwise we have a contradiction.
      rcases quot.exists_rep ys with ⟨ ys, ⟨ _ ⟩ ⟩,
      cases ys,
      case list.nil { from rfl },
      case list.cons : y ys { cases erev y (multiset.mem_cons_self y ys) },
    },

    case list.cons : x xs ih {
      -- If we have some x∷xs, then we must have some y∷ys such that x ≃ y.
      -- By induction we have that map f xs = map g ys.
      -- However, constructing the inductive case is a little annoying, as we
      -- need to show ∀ x, x ∈ xs ↔ x⁻¹ ∈ ys

      -- TODO: Could we express the two function as the above, and make use
      -- of the isomorphism for everything else? If so, does it make anything
      -- simpler?

      have ymem := efwd x (multiset.mem_cons_self x xs),
      rcases multiset.exists_cons_of_mem ymem with ⟨ ys, ⟨ _ ⟩ ⟩,

      suffices
        : multiset.map (λ x, f x) (x :: quot.mk setoid.r xs)
        = multiset.map (λ x, g x) (iso.to_fun x :: ys),
        from this,
      simp only [add_zero, multiset.map_cons],

      suffices : multiset.map f (quot.mk setoid.r xs)
               = multiset.map g ys,
        refine congr_arg2 _ (feq x) this,

      have nodupx' : multiset.nodup (quot.mk setoid.r xs),
        have eq := multiset.cons_coe x xs,
        unfold_coes at eq, rw ← eq at nodupx,
        from (multiset.nodup_cons.mp nodupx).2,
      have nodupy' := (multiset.nodup_cons.mp nodupy).2,

      refine ih nodupx' ys nodupy' _ _,

      show ∀ x, x ∈ finset.mk xs nodupx' → iso.to_fun x ∈ finset.mk ys nodupy', assume z mem,
        have mem_xxs : z ∈ finset.mk (quot.mk setoid.r (x :: xs)) nodupx,
          have : z ∈ quot.mk _ xs := mem,
          from multiset.mem_cons_of_mem this,

        have mem_yys : iso.to_fun z ∈ finset.mk (iso.to_fun x :: ys) _
          := efwd _ mem_xxs,

        have : iso.to_fun z = iso.to_fun x ∨ iso.to_fun z ∈ ys := multiset.mem_cons.1 mem_yys,
        cases this,
        case or.inr { from this },
        case or.inl {
          have : z = x := equiv.injective iso this, subst ‹z = x›,
          have eq := multiset.cons_coe z xs,
          unfold_coes at eq, rw ← eq at nodupx,
          from absurd mem (multiset.nodup_cons.mp nodupx).1,
        },

      show ∀ y, y ∈ finset.mk ys nodupy' → iso.inv_fun y ∈ finset.mk xs nodupx', assume z mem,
        have mem_yys : z ∈ finset.mk (iso.to_fun x :: ys) nodupy,
          from multiset.mem_cons_of_mem mem,

        have mem_xxs : iso.inv_fun z ∈ (x :: (xs : multiset _)) := erev _ mem_yys,
        have : iso.inv_fun z = x ∨ iso.inv_fun z ∈ xs := multiset.mem_cons.1 mem_xxs,
        cases this,
        case or.inr { from this },
        case or.inl {
          subst this,
          have : z ∉ ys, { rw ←iso.right_inv z, from (multiset.nodup_cons.mp nodupy).1 },
          from absurd ‹z ∈ ys› ‹z ∉ ys›,
        },
    },
  },
  { from rfl }
end

/-- finset.map_iso but for sum_map. -/
lemma multiset.sum_map_iso {α₁ α₂ β: Type} [add_comm_monoid β]
    (f : α₁ → β) (g : α₂ → β) (iso : α₁ ≃ α₂)
    (feq : ∀ x, f x = g (iso.to_fun x))
    (xs : finset α₁) (ys : finset α₂)
  : (∀ x, x ∈ xs → iso.to_fun x ∈ ys)
  → (∀ y, y ∈ ys → iso.inv_fun y ∈ xs)
  → multiset.sum_map f xs.val = multiset.sum_map g ys.val
| mem mem' := congr_arg _ (finset.map_iso f g iso feq xs ys mem mem')

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

/-- Partition a multiset into two multisets. -/
def multiset.partition_map {α β γ : Type} (f : α → β ⊕ γ) (xs : multiset α) : multiset β × multiset γ
  := quot.lift_on xs
    (λ x, prod.mk ((list.partition_map f x).1 : multiset β)
                  ((list.partition_map f x).2 : multiset γ))
    (λ x y perm, begin
      simp only [prod.mk.inj_iff, multiset.coe_eq_coe],
      from list.perm_partition_map f perm,
    end)

lemma multiset.partition_map_append {α β γ : Type} (f : α → β ⊕ γ) :
  ∀ (xs : multiset α)
  , multiset.map sum.inl (multiset.partition_map f xs).1 + multiset.map sum.inr (multiset.partition_map f xs).2
  = multiset.map f xs
| xs := begin
  rcases quot.exists_rep xs with ⟨ xs, ⟨ _ ⟩ ⟩,
  from quot.sound (list.partition_map_append f xs),
end

lemma multiset.partition_map_map {α β γ δ : Type} (f : δ → β ⊕ γ) (g : α → δ):
  ∀ (xs : multiset α)
  , multiset.partition_map (f ∘ g) xs = multiset.partition_map f (multiset.map g xs)
| xs := begin
  rcases quot.exists_rep xs with ⟨ xs, ⟨ _ ⟩ ⟩,
  simp only [multiset.map, multiset.partition_map, quot.lift_on], unfold_coes,
  rw list.partition_map_map f g xs,
end

lemma multiset.partition_map_map_id {α β γ : Type} (f : α → β ⊕ γ) :
  ∀ (xs : multiset α)
  , multiset.partition_map f xs = multiset.partition_map id (multiset.map f xs)
| xs := multiset.partition_map_map id f xs

/-- Partition a multiset into two multisets. -/
def finset.partition_map {α β γ : Type} (f : α ↪ β ⊕ γ) : finset α → finset β × finset γ
| ⟨ xs, nodup ⟩ := begin
  refine ⟨ ⟨ (xs.partition_map f.1).1, _ ⟩, ⟨ (xs.partition_map f.1).2, _ ⟩ ⟩,
  apply quot.induction_on xs,
  simp only [multiset.partition_map],
  sorry, sorry,
end

#lint-

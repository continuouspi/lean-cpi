import data.list.perm logic.embedding

namespace list

/-- Show that partition_map holds over filters -/
lemma perm_partition_map {α β γ : Type} (f : α → β ⊕ γ) :
  ∀ {xs ys : list α}, xs ~ ys
  → (partition_map f xs).1 ~ (partition_map f ys).1
  ∧ (partition_map f xs).2 ~ (partition_map f ys).2
| xs ys p := begin
  induction p,
  case perm.nil { from ⟨ perm.nil, perm.nil ⟩ },
  case perm.skip : x xs ys p ih {
    cases ih with p₁ p₂,
    simp only [partition_map],
    cases f x,
    all_goals {
      simp only [partition_map._match_1],
      cases (partition_map f xs) with xs₁ xs₂,
      cases (partition_map f ys) with xs₁ xs₂,
    },
    from ⟨ perm.skip _ p₁, p₂ ⟩,
    from ⟨ p₁, perm.skip _ p₂ ⟩,
  },
  case perm.swap : x y xs {
    simp only [partition_map],
    cases f x with val₁ val₁; cases f y with val₂ val₂,
    all_goals {
      simp only [partition_map._match_1],
      cases (partition_map f xs) with xs₁ xs₂,
    },
    from ⟨ perm.swap _ _ xs₁, perm.refl xs₂ ⟩,
    from ⟨ perm.skip _ (perm.refl xs₁), perm.skip _ (perm.refl xs₂) ⟩,
    from ⟨ perm.skip _ (perm.refl xs₁), perm.skip _ (perm.refl xs₂) ⟩,
    from ⟨ perm.refl xs₁, perm.swap _ _ xs₂ ⟩,
  },
  case perm.trans : xs ys zs xy yz ihxy ihyz {
    cases ihxy with xy₁ xy₂, cases ihyz with yz₁ yz₂,
    from ⟨ perm.trans xy₁ yz₁, perm.trans xy₂ yz₂ ⟩,
  },
end

/-- Show that partitioning and then joining gives the same as appending in the
    first place. -/
lemma partition_map_append {α β γ : Type} (f : α → β ⊕ γ):
  ∀ (xs : list α)
  , map sum.inl (partition_map f xs).1 ++ map sum.inr (partition_map f xs).2
  ~ map f xs
| [] := by simp only [partition_map, append_nil, map]
| (x :: xs) := begin
  simp only [partition_map, map],
  have h := partition_map_append xs,
  cases (partition_map f xs) with xs₁ xs₂,
  cases f x;
  simp only [partition_map._match_1, prod.map, id, map_cons],
  case sum.inl { from perm.skip _ h },
  case sum.inr { from perm.trans perm_middle (perm.skip _ h) },
end

/-- Show that partition_map is just partitioning and mapping. -/
lemma partition_map_map {α β γ δ : Type} (f : δ → β ⊕ γ) (g : α → δ) :
  ∀ (xs : list α)
  , partition_map (f ∘ g) xs = partition_map f (map g xs)
| [] := by simp only [partition_map, map]
| (x :: xs) := by { simp only [partition_map, map], rw ← partition_map_map xs }

/-- Show that partition_map is just partitioning and mapping. -/
lemma partition_map_map_id {α β γ : Type} (f : α → β ⊕ γ) :
  ∀ (xs : list α)
  , partition_map f xs = partition_map id (map f xs)
| xs := partition_map_map id f xs

/-- Show that partition_map is just partitioning and mapping. -/
-- lemma partition_map_nodup {α β γ : Type} (f : α ↪ β ⊕ γ) :
--   ∀ {xs : list α}
--   , nodup xs → nodup (partition_map f.1 xs).1 ∧ nodup (partition_map f.1 xs).2
-- | xs nd := begin
--   induction xs,
--   case nil { from ⟨ nodup_nil, nodup_nil ⟩ },
--   case cons : x xs ih {
--     simp only [partition_map],

--     cases (partition_map f.1 xs) with xs₁ xs₂,
--     cases h : f.to_fun x, simp only [partition_map._match_1, prod.map, id],
--     rcases ih (pairwise_of_pairwise_cons nd) with ⟨ nd₁, nd₂ ⟩,

--     refine ⟨ nodup_cons.mpr ⟨ _, nd₁ ⟩, nd₂ ⟩,
--     assume mem,

--   }
-- end

end list

#lint-

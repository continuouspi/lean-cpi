namespace list

variables {α β γ : Type}

def map_witness : ∀ (l : list α), (Π x ∈ l, β) → list β
| [] _ := []
| (x :: xs) f
  := f x (mem_cons_self x xs)
  :: map_witness xs (λ x' mem, f x' (mem_cons_of_mem x mem))

lemma map_witness_mem :
  ∀ {l : list α} {x : α} (f : Π x ∈ l, β) (mem : x ∈ l)
  , f x mem ∈ map_witness l f
| [] x f mem := not_mem_nil x mem
| (x :: xs) x' f mem :=
  match mem with
  | or.inl here := by simp [map_witness, here]
  | or.inr there := begin
      simp [map_witness],
      from or.inr (map_witness_mem _ there)
    end
  end

lemma map_witness_to_map (f : α → β) :
  ∀ (l : list α), map_witness l (λ x _, f x) = map f l
| [] := rfl
| (x :: xs) := by { simp [map_witness], from map_witness_to_map xs }

@[simp]
lemma map_witness_id (l : list α) : map_witness l (λ x _, x) = l := begin
  have h : (λ (x : α), x) = id := rfl,
  rw [map_witness_to_map _ l, h],
  simp
end

@[simp]
lemma map_witness_map :
  ∀ (l : list α) (f : (Π x ∈ l, β)) (g : β → γ)
  , map g (map_witness l f) = map_witness l (λ a mem, g (f a mem))
| [] _ _ := rfl
| (x :: xs) f g := by { simp [map_witness, map], from map_witness_map xs _ g }

-- @[simp]
-- lemma map_witness_map_witness :
--   ∀ (l : list α) (f : Π x ∈ l, β) (g : Π x ∈ map_witness l f, γ)
--   , map_witness (map_witness l f) g
--   = map_witness l (λ a mem, g (f a mem) (map_witness_mem f mem))
-- | [] _ _ := rfl
-- | (x :: xs) f g := by {
--     simp [map_witness],
--   }

end list

/- A definition of unordered pairs.

   This follows the same form as "Theorem Proving in Lean" [1]. We define a
   pair where both elements are the same type, an equivalency relationship over
   them. This is used to build a quotient, which represents our actual pair.

   [1]: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients-/

import tactic.sanity_check tactic.tidy

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

universe u

namespace upair
  variable {α : Type u}

  protected structure pair (α : Type u) := (fst snd : α)

  protected def equiv : pair α → pair α → Prop
  | ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ := (a₁ = a₂ ∧ b₁ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁)

  private lemma equiv_refl : ∀ (p : pair α), upair.equiv p p
  | ⟨ a, b ⟩ := or.inl ⟨ rfl, rfl ⟩

  private lemma equiv_symm : ∀ (p q : pair α), upair.equiv p q → upair.equiv q p
  | ⟨ a, b ⟩ ⟨ _, _ ⟩ (or.inl ⟨ rfl, rfl ⟩):= or.inl ⟨ rfl, rfl ⟩
  | ⟨ a, b ⟩ ⟨ _, _ ⟩ (or.inr ⟨ rfl, rfl ⟩):= or.inr ⟨ rfl, rfl ⟩

  private lemma equiv_trans : ∀ (p q r : pair α), upair.equiv p q → upair.equiv q r → upair.equiv p r
  | ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ ⟨ a₃, b₃ ⟩ p q := begin
    rcases p with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩;
    rcases q with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩;
    { from or.inl ⟨ rfl, rfl ⟩ <|> from or.inr ⟨ rfl, rfl ⟩ }
  end

  private lemma is_equiv : equivalence (@upair.equiv α)
    := ⟨ equiv_refl, equiv_symm, equiv_trans ⟩

  instance setoid : setoid (pair α) := setoid.mk upair.equiv is_equiv
end upair

def upair (α : Type u) : Type u := quotient (@upair.setoid α)

namespace upair
  protected def mk {α : Type u} (a b : α) : upair α := ⟦ ⟨ a, b ⟩ ⟧

  private def pair_map {α β : Type u} (f : α → β) : pair α → pair β
  | ⟨ a, b ⟩ := ⟨ f a, f b ⟩

  private def pair_map_eq {α β : Type u} (f : α → β) :
    ∀ {a b : pair α}, a ≈ b → pair_map f a ≈ pair_map f b
  | ⟨ a, b ⟩ ⟨ _, _ ⟩ (or.inl ⟨ rfl, rfl ⟩) := or.inl ⟨ rfl, rfl ⟩
  | ⟨ a, b ⟩ ⟨ _, _ ⟩ (or.inr ⟨ rfl, rfl ⟩) := or.inr ⟨ rfl, rfl ⟩

  protected def map {α β : Type u} (f : α → β) (p : upair α) : upair β
    := quot.lift_on p (λ x, ⟦ pair_map f x ⟧) (λ _ _ p, quot.sound (pair_map_eq f p))

end upair

#sanity_check

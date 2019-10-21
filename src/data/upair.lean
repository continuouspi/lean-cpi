/- A definition of unordered pairs.

   This follows the same form as "Theorem Proving in Lean" [1]. We define a
   pair where both elements are the same type, an equivalency relationship over
   them. This is used to build a quotient, which represents our actual pair.

   [1]: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients-/

import tactic.lint tactic.tidy data.quot

run_cmd lint
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

  protected lemma eq {α : Type} (a b : α) : upair.mk a b = upair.mk b a
    := quot.sound (or.inr ⟨rfl, rfl⟩)

  private def pair_map {α β : Type u} (f : α → β) : pair α → pair β
  | ⟨ a, b ⟩ := ⟨ f a, f b ⟩

  private def pair_map_eq {α β : Type u} (f : α → β) :
    ∀ {a b : pair α}, a ≈ b → pair_map f a ≈ pair_map f b
  | ⟨ a, b ⟩ ⟨ _, _ ⟩ (or.inl ⟨ rfl, rfl ⟩) := or.inl ⟨ rfl, rfl ⟩
  | ⟨ a, b ⟩ ⟨ _, _ ⟩ (or.inr ⟨ rfl, rfl ⟩) := or.inr ⟨ rfl, rfl ⟩

  protected def map {α β : Type u} (f : α → β) (p : upair α) : upair β
    := quot.lift_on p (λ x, ⟦ pair_map f x ⟧) (λ _ _ p, quot.sound (pair_map_eq f p))

  protected lemma map_compose {α β γ : Type u} (f : α → β) (g : β → γ) (p : upair α)
    : upair.map g (upair.map f p) = upair.map (g ∘ f) p
    := quot.rec_on p (λ ⟨ a, b ⟩, quot.sound (or.inl ⟨ rfl, rfl ⟩)) (λ _ _ _, rfl)

  protected lemma map_identity {α : Type u} (p : upair α)
    : upair.map id p = p := begin
      rcases quot.exists_rep p with ⟨ ⟨ a, b ⟩, ⟨ _ ⟩ ⟩,
      from quot.sound (or.inl ⟨ rfl, rfl ⟩)
    end

  protected lemma map_id {α : Type u} : upair.map (@id α) = id := funext upair.map_identity

  protected lemma map.inj {α β : Type u} {f : α → β}
    (inj : function.injective f) :
    ∀ {p q : upair α}, upair.map f p = upair.map f q → p = q
  | p q eq := begin
    rcases quot.exists_rep p with ⟨ ⟨ a₁, b₁ ⟩, ⟨ _ ⟩ ⟩,
    rcases quot.exists_rep q with ⟨ ⟨ a₂, b₂ ⟩, ⟨ _ ⟩ ⟩,

    have eq' : ⟦pair_map f ⟨ a₁, b₁ ⟩⟧ = ⟦pair_map f ⟨ a₂, b₂ ⟩⟧,
      have h := quot.lift_beta (λ x, ⟦ pair_map f x ⟧) (λ _ _ p, quot.sound (pair_map_eq f p)) ⟨ a₁, b₁ ⟩,
      have g := quot.lift_beta (λ x, ⟦ pair_map f x ⟧) (λ _ _ p, quot.sound (pair_map_eq f p)) ⟨ a₂, b₂ ⟩,
      from trans (symm h) (trans eq g),

    cases quotient.exact eq',
    case or.inl : h { cases inj h.1, cases inj h.2, from rfl },
    case or.inr : h { cases inj h.1, cases inj h.2, from quot.sound (or.inr ⟨ rfl, rfl ⟩) },
  end

  protected lemma map_beta
    {α β : Type u} (f : α → β) (a b : α)
    : upair.map f (upair.mk a b) = upair.mk (f a) (f b)
    := quot.sound (or.inl ⟨ rfl, rfl ⟩)

end upair

#lint

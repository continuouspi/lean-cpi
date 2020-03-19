/- A definition of unordered pairs.

   This follows the same form as "Theorem Proving in Lean" [1]. We define a
   pair where both elements are the same type, an equivalency relationship over
   them. This is used to build a quotient, which represents our actual pair.

   [1]: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients-/

import tactic.lint tactic.basic data.quot logic.function data.string.basic

namespace upair
  variable {α : Type*}

  /-- A pair of items, both of the same type. -/
  @[nolint has_inhabited_instance]
  protected structure pair (α : Type*) := (fst snd : α)

  instance pair.has_repr (α : Type*) [has_repr α] : has_repr (upair.pair α)
    := ⟨ λ x, repr x.1 ++ " , " ++ repr x.2 ⟩

  /-- Two pairs are equivalent if they are equal or equal when swapped. -/
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

  instance decidable_rel [decidable_eq α] : decidable_rel (@upair.equiv α)
  | ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ := by { unfold upair.equiv, apply_instance }
end upair

/-- An unordered pair of items. -/
@[nolint has_inhabited_instance]
def upair (α : Type*) : Type* := quotient (@upair.setoid α)

namespace upair
  variables {α : Type*} {β : Type*}

  /-- Construct a new unordered pair. -/
  protected def mk (a b : α) : upair α := ⟦ ⟨ a, b ⟩ ⟧

  protected lemma mk.comm (a b : α) : upair.mk a b = upair.mk b a
    := quot.sound (or.inr ⟨ rfl, rfl ⟩)

  protected lemma exists_rep (p : upair α) : ∃ (a b : α), upair.mk a b = p
    := let ⟨ ⟨ a, b ⟩, e ⟩ := quot.exists_rep p in ⟨ a, b, e ⟩

  instance [decidable_eq α] : decidable_eq (upair α) := quotient.decidable_eq

  /-- Apply a symmetric function to the contents of this pair. -/
  protected def lift (f : α → α → β)
    : (∀ a b, f a b = f b a) → upair α → β
  | comm p := quot.lift_on p (λ p, f p.fst p.snd) (λ ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ r, begin
    rcases r with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
    from rfl, from comm _ _,
  end)

  /-- Apply a symmetric function to the contents of this pair. Just `upair.lift`, but in a more type-inference friendly
      order-/
  protected def lift_on (q : upair α) (f : α → α → β) (h : ∀ a b, f a b = f b a) : β
    := upair.lift f h q

  instance {α : Type*} [has_repr α] : has_repr (upair α) := ⟨ λ x,
    upair.lift_on x (λ x y, min (repr (pair.mk x y)) (repr (pair.mk y x))) (λ x y, min_comm _ _)⟩

  protected lemma lift.inj (f : α → α → β) (h : (∀ a b, f a b = f b a))
      (inj : ∀ ⦃a b a' b'⦄, f a b = f a' b' → pair.mk a b ≈ pair.mk a' b')
    : function.injective (upair.lift f h)
  | p q eql := begin
    rcases quot.exists_rep p with ⟨ ⟨ a₁, b₁ ⟩, e ⟩, subst e,
    rcases quot.exists_rep q with ⟨ ⟨ a₂, b₂ ⟩, e ⟩, subst e,
    from quot.sound (inj eql),
  end

  @[simp]
  protected lemma lift_on_beta (f : α → α → β) (c : ∀ (a b : α), f a b = f b a) {a b : α}
    : upair.lift_on (upair.mk a b) f c = f a b
    := rfl

  /-- A bit like `lift_on`, but polymorphic in the return type. -/
  @[reducible, elab_as_eliminator]
  protected def rec_on {β : upair α → Sort*} (q : upair α) (f : ∀ a b, β (upair.mk a b))
    (c : ∀ (a b : α), f a b == f b a) : β q
  := quotient.hrec_on q (λ ⟨ a, b ⟩, f a b) (λ ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ r, begin
    show f a₁ b₁ == f a₂ b₂,
    rcases r with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
    from heq.rfl, from c a₁ b₁,
  end)

  @[simp]
  protected lemma rec_on_beta {β : upair α → Sort*} {a b : α} (f : ∀ a b, β (upair.mk a b))
      (c : ∀ (a b : α), f a b == f b a)
    : @upair.rec_on α β (upair.mk a b) f c = f a b
    := rfl

  protected lemma rec_on.inj {β : upair α → Sort*} {f : ∀ a b, β (upair.mk a b)}
      (c : ∀ (a b : α), f a b == f b a)
      (inj : ∀ ⦃a b a' b'⦄, f a b == f a' b' → pair.mk a b ≈ pair.mk a' b')
  : ∀ p q
  , @upair.rec_on α β p f c == @upair.rec_on α β q f c
  → p = q
  | p q eql := begin
    rcases quot.exists_rep p with ⟨ ⟨ a₁, b₁ ⟩, e ⟩, subst e,
    rcases quot.exists_rep q with ⟨ ⟨ a₂, b₂ ⟩, e ⟩, subst e,
    from quot.sound (inj eql),
  end

  protected lemma eq (a b : α) : upair.mk a b = upair.mk b a
    := quot.sound (or.inr ⟨rfl, rfl⟩)

  /-- Map over the contents of an unordered pair. -/
  protected def map (f : α → β) (p : upair α) : upair β
    := upair.lift_on p (λ x y, upair.mk (f x) (f y)) (λ x y, mk.comm _ _ )

  @[simp]
  protected lemma map_compose {γ : Type*} (f : α → β) (g : β → γ) (p : upair α)
    : upair.map g (upair.map f p) = upair.map (g ∘ f) p
    := quot.rec_on p (λ ⟨ a, b ⟩, quot.sound (or.inl ⟨ rfl, rfl ⟩)) (λ _ _ _, rfl)

  @[simp]
  protected lemma map_identity (p : upair α)
    : upair.map id p = p := begin
      rcases quot.exists_rep p with ⟨ ⟨ a, b ⟩, ⟨ _ ⟩ ⟩,
      from quot.sound (or.inl ⟨ rfl, rfl ⟩)
    end

  protected lemma map_id : upair.map (@id α) = id := funext upair.map_identity

  protected lemma map.inj {f : α → β}
    (inj : function.injective f) :
    ∀ {p q : upair α}, upair.map f p = upair.map f q → p = q
  | p q eq := begin
    suffices : ∀ (a b a' b' : α), upair.mk (f a) (f b) = upair.mk (f a') (f b') → pair.mk a b ≈ pair.mk a' b',
      from lift.inj _ _ this eq,

    assume a₁ b₁ a₂ b₂ eql,
    refine or.imp _ _ (quotient.exact eql); from (λ x, ⟨ inj x.1, inj x.2 ⟩),
  end

  @[simp]
  protected lemma map_beta (f : α → β) (a b : α)
    : upair.map f (upair.mk a b) = upair.mk (f a) (f b)
    := quot.sound (or.inl ⟨ rfl, rfl ⟩)
end upair

#lint-

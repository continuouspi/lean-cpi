/- A definition of unordered pairs.

   This follows the same form as "Theorem Proving in Lean" [1]. We define a
   pair where both elements are the same type, an equivalency relationship over
   them. This is used to build a quotient, which represents our actual pair.

   [1]: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients-/

import tactic.lint tactic.basic data.quot logic.function data.string.basic

universe u

namespace upair
  variable {α : Type u}

  /-- A pair of items, both of the same type. -/
  @[nolint has_inhabited_instance]
  protected structure pair (α : Type u) := (fst snd : α)

  instance pair.has_repr (α : Type u) [has_repr α] : has_repr (upair.pair α)
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
def upair (α : Type u) : Type u := quotient (@upair.setoid α)

namespace upair
  variables {α : Type*} {β : Type*}

  /-- Construct a new unordered pair. -/
  protected def mk (a b : α) : upair α := ⟦ ⟨ a, b ⟩ ⟧

  protected lemma mk.comm (a b : α) : upair.mk a b = upair.mk b a
    := quot.sound (or.inr ⟨ rfl, rfl ⟩)

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

  instance {α : Type u} [has_repr α] : has_repr (upair α) := ⟨ λ x,
    upair.lift_on x (λ x y, min (repr (pair.mk x y)) (repr (pair.mk y x))) (λ x y, min_comm _ _)⟩

  protected lemma lift.inj (f : α → α → β) (h : (∀ a b, f a b = f b a))
      (inj : ∀ ⦃a b a' b'⦄, f a b = f a' b' → pair.mk a b ≈ pair.mk a' b')
    : function.injective (upair.lift f h)
  | p q eql := begin
    rcases quot.exists_rep p with ⟨ ⟨ a₁, b₁ ⟩, e ⟩, subst e,
    rcases quot.exists_rep q with ⟨ ⟨ a₂, b₂ ⟩, e ⟩, subst e,
    from quot.sound (inj eql),
  end

  /-- A bit like `lift_on`, but polymorphic in the return type. -/
  @[reducible, elab_as_eliminator]
  protected def rec_on {β : upair α → Sort*} (q : upair α) (f : ∀ a b, β (upair.mk a b))
    (c : ∀ (a b : α), f a b == f b a) : β q
  := quotient.hrec_on q (λ ⟨ a, b ⟩, f a b) (λ ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ r, begin
    show f a₁ b₁ == f a₂ b₂,
    rcases r with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
    from heq.rfl, from c a₁ b₁,
  end)

  protected lemma rec_on_mk {β : upair α → Sort*} {a b : α} (f : ∀ a b, β (upair.mk a b))
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

  protected lemma eq {α : Type} (a b : α) : upair.mk a b = upair.mk b a
    := quot.sound (or.inr ⟨rfl, rfl⟩)

  /-- Map over the contents of an unordered pair. -/
  protected def map {α β : Type u} (f : α → β) (p : upair α) : upair β
    := upair.lift_on p (λ x y, upair.mk (f x) (f y)) (λ x y, mk.comm _ _ )

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
    suffices : ∀ (a b a' b' : α), upair.mk (f a) (f b) = upair.mk (f a') (f b') → pair.mk a b ≈ pair.mk a' b',
      from lift.inj _ _ this eq,

    assume a₁ b₁ a₂ b₂ eql,
    refine or.imp _ _ (quotient.exact eql); from (λ x, ⟨ inj x.1, inj x.2 ⟩),
  end

  protected lemma map_beta
    {α β : Type u} (f : α → β) (a b : α)
    : upair.map f (upair.mk a b) = upair.mk (f a) (f b)
    := quot.sound (or.inl ⟨ rfl, rfl ⟩)

  private def do_unpair₁ {α β : Type u} [decidable_eq β] (f : α → β) {a : α} {b : β}
    : ∀ {p : pair α}
    , upair.map f (quot.mk setoid.r p) = upair.mk (f a) b → Σ' b', f b' = b
  | ⟨ a', b' ⟩ eq :=
    if eqA : (f a' = b) then ⟨ a', eqA ⟩
    else if eqB : (f b' = b) then ⟨ b', eqB ⟩
    else false.elim (or.elim (quotient.exact eq) (λ x, eqB x.2) (λ x, eqA x.1))

  /-- unpair₁ provides a mechanism to extract elements from a pair which is the
      result of mapping over a pair of known values. -/
  protected def unpair₁
      {α β : Type u} [deq : decidable_eq β] {f : α → β} (inj : function.injective f)
    : ∀ {a : α} {b : β} {p : upair α}
    , upair.map f p = upair.mk (f a) b → Σ' b', f b' = b
  | a b p eq := quot.hrec_on p
      (λ p eq, do_unpair₁ f eq)
      (λ ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ r, function.hfunext
        (congr_arg (λ x, upair.map f x = upair.mk (f a) b) (quot.sound r))
        (λ eqA eqB eqEq, begin
          clear _fun_match _fun_match _x _x eq,

          simp only [heq_iff_eq],
          rcases r with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
          { from rfl },
          {
            unfold do_unpair₁ dite upair.map,
            rcases quotient.exact eqA with ⟨ eqA, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, eqB ⟩,
            {
              cases (deq (f a₁) (f b₁)),
              case is_true : is_eq {
                cases inj is_eq,
                have : (deq (f a₁) (f a₁)) = is_true rfl := subsingleton.elim _ _,
                rw this,
              },
              case is_false { simp },
            },
            {
              cases (deq (f a₁) (f b₁)),
              case is_true : is_eq {
                cases inj is_eq,
                have : (deq (f a₁) (f a₁)) = is_true rfl := subsingleton.elim _ _,
                rw this,
              },
              case is_false {
                have : (deq (f b₁) (f a₁)) = is_false (ne.symm h) := subsingleton.elim _ _,
                rw this,
              },
            }

          }
        end))
      eq
end upair

#lint-

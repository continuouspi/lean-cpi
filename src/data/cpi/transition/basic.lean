import data.cpi.transition.lookup data.cpi.transition.production

namespace cpi

variables {ℍ : Type} {ω : context}

/-- A transition from one species to a production. This represents the potential
    for a reaction. The label indicates the kind of reaction (spontantious or
    communicating). -/
@[nolint has_inhabited_instance]
inductive transition :
  Π {Γ} {k}
  , species ℍ ω Γ → lookup ℍ ω Γ → label ℍ Γ k → production ℍ ω Γ k
  → Type

/- Additional transition to project project into where our choiceₙ rules apply. -/
| ξ_choice
    {Γ ℓ f} {π : prefix_expr ℍ Γ f} {A : species ℍ ω (f.apply Γ)} {As : species.choices ℍ ω Γ}
    {k} {l : label ℍ Γ k} {E : production ℍ ω Γ k}

  : transition (Σ# As) ℓ l E
  → transition (Σ# species.whole.cons π A As) ℓ l E

| choice₁
    {Γ ℓ}

    (a : name Γ) (b : list (name Γ)) (y : ℕ) (A : species ℍ ω (context.extend y Γ))
    (As : species.choices ℍ ω Γ)
  : transition (Σ# species.whole.cons (a#(b; y)) A As)
               ℓ (#a)
               (#(⟨ b, rfl ⟩; y) A)
| choice₂
    {Γ ℓ}

    (k : ℍ) (A : species ℍ ω Γ) (As : species.choices ℍ ω Γ)
  : transition (Σ# species.whole.cons (τ@k) A As) ℓ τ@'k A

| com₁
    {Γ ℓ x y} {A B : species ℍ ω Γ} {a b : name Γ}
    {F : concretion ℍ ω Γ x y} {G : concretion ℍ ω Γ y x}

  : transition A ℓ (#a) F
  → transition B ℓ (#b) G
  → transition (A |ₛ B) ℓ τ⟨ a, b ⟩ (concretion.pseudo_apply F G)

| com₂
    {Γ ℓ} (M : affinity ℍ) {a b : fin M.arity}
    {A B : species ℍ ω (context.extend M.arity Γ)}

    (k : option.is_some (M.f a b))
  : transition A (lookup.rename name.extend ℓ) τ⟨ name.zero a, name.zero b ⟩ B
  → transition (ν(M) A) ℓ τ@'(option.get k) (ν(M) B)

| parₗ
    {Γ ℓ} {A : species ℍ ω Γ} (B : species ℍ ω Γ)
    {k} {l : label ℍ Γ k} {E}

  : transition A ℓ l E
  → transition (A |ₛ B) ℓ l (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E)
| parᵣ
    {Γ ℓ} (A : species ℍ ω Γ) {B : species ℍ ω Γ}
    {k} {l : label ℍ Γ k} {E}

  : transition B ℓ l E
  → transition (A |ₛ B) ℓ l (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E)

| ν₁
    {Γ ℓ} (M : affinity ℍ) {A : species ℍ ω (context.extend M.arity Γ)}
    {k} {l : label ℍ Γ k} {E : production ℍ ω (context.extend M.arity Γ) k}

  : transition A (lookup.rename name.extend ℓ) (label.rename name.extend l) E
  → transition (ν(M) A) ℓ l (production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E)


| defn
    {Γ k n} {α : label ℍ (context.extend n Γ) k}
    (ℓ : ∀ n, reference n ω → species.choices ℍ ω (context.extend n Γ))
    {E}
    (D : reference n ω) (as : vector (name Γ) n)
  : transition (Σ# (ℓ n D)) (lookup.rename name.extend ℓ) α E
  → transition
      (species.apply D as)
      ℓ
      (label.rename (name.mk_apply as) α)
      (production.rename (name.mk_apply as) E)

notation A ` [`:max ℓ `, ` α `]⟶ ` E:max := transition A ℓ α E

namespace transition
  private lemma congr_arg_heq₂
      {α} {β γ : α → Sort*} (f : ∀ a, β a → γ a)
    : ∀ {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, a₁ = a₂ → b₁ == b₂ → f a₁ b₁ == f a₂ b₂
  | a _ b _ rfl heq.rfl := heq.rfl

  /-- Rename a transition.

      This definition is a little complex, in that it returns a pair of the
      transition, its label/output and equalities relating the renamed
      label/outputs to the original. This makes the proof a bit simpler in
      places,  as we don't need to worry about some of the more complex
      equalities.
      Mostly it's like this because I thought I needed this instead of
      rename_from - I was wrong. -/
  protected def rename_to :
    ∀ {Γ Δ ℓ k}
      {A : species ℍ ω Γ} {l : label ℍ Γ k} {E : production ℍ ω Γ k}
      (ρ : name Γ → name Δ)
    , A [ℓ, l]⟶ E
    → Σ' (l' : label ℍ Δ k) (E' : production ℍ ω Δ k)
    , pprod ((species.rename ρ A) [lookup.rename ρ ℓ, l']⟶ E')
            (label.rename ρ l = l' ∧ production.rename ρ E = E')
  | Γ Δ ℓ k A l E ρ t := begin
    induction t generalizing Δ,

    case ξ_choice : Γ ℓ f π A As k l E t ih {
      rcases ih _ ρ with ⟨ l', E', t', eql, eqE ⟩,
      simp only [species.rename.choice, species.rename.cons] at t' ⊢,
      from ⟨ l', E', ξ_choice t', eql, eqE ⟩,
    },

    case choice₁ : Γ ℓ a b y A As {
      simp only [ rename.choice, rename.cons,
                  prefix_expr.ext_communicate, prefix_expr.rename_communicate,
                  list.length, list.map ],

      suffices
        : production.rename ρ (↑#(⟨b, _⟩ ; y)A)
        = ↑#(⟨list.map ρ b, _⟩ ; y)species.rename (name.ext ρ) A,
        from ⟨ _, _, choice₁ (ρ a) (list.map ρ b) y (species.rename _ A) (species.rename ρ As), rfl, this ⟩,
      unfold_coes,
      simp [list.length_map, production.rename, concretion.rename, vector.map],

      have : list.length (list.map ρ b) = list.length b := list.length_map _ _,
      refine congr_arg_heq₂ (λ XX YY, @concretion.apply ℍ ω Δ XX
          (@subtype.mk (list (name Δ))
            (λ (l : list (name Δ)), list.length l = XX)
            (list.map ρ b)
            YY )
          y
          (species.rename (name.ext ρ) A)) (symm this) _,
      simp only [list.length_map, iff_self, eq_iff_iff, eq_mpr_heq],
    },

    case choice₂ : Γ ℓ k A As {
      simp only [species.rename.choice, species.rename.cons],
      from ⟨ τ@'k, _, choice₂ k (species.rename ρ A) (species.rename ρ As), rfl, rfl ⟩
    },

    case com₁ : Γ ℓ x y A B a b F G tf tg ihf ihg {
      simp only [species.rename.parallel],
      rcases ihf _ ρ with ⟨ _, _, tf', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      rcases ihg _ ρ with ⟨ _, _, tg', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from ⟨ τ⟨ ρ a, ρ b ⟩, _, com₁ tf' tg', rfl,
             congr_arg production.species (concretion.pseudo_apply.rename ρ F G) ⟩
    },

    case com₂ : Γ ℓ M a b A B k t ih {
      simp only [species.rename.restriction],
      rcases ih _ (name.ext ρ) with ⟨ _, _, tf', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at tf',
      from ⟨ _, _, com₂ M k tf', rfl,
             congr_arg production.species (species.rename.restriction M _) ⟩,
    },

    case parₗ : Γ ℓ A B k l E t ih {
      simp only [species.rename.parallel],
      rcases ih _ ρ with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      refine ⟨ label.rename ρ l, _, parₗ _ t', rfl, _ ⟩,
      cases E,
      case production.concretion { from rfl },
      case production.species {
        from congr_arg production.species (species.rename.parallel _ _),
      }
    },

    case parᵣ : Γ ℓ A B k l E t ih {
      simp only [species.rename.parallel],
      rcases ih _ ρ with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      refine ⟨ label.rename ρ l, _, parᵣ _ t', rfl, _ ⟩,
      cases E,
      case production.concretion { from rfl },
      case production.species {
        from congr_arg production.species (species.rename.parallel _ _),
      }
    },

    case ν₁ : Γ ℓ M A k l E t ih {
      simp only [species.rename.restriction],
      rcases ih _ (name.ext ρ) with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      rw [label.rename_compose, name.ext_extend, ← label.rename_compose] at t',
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at t',
      refine ⟨ _, _, ν₁ M t', rfl, _ ⟩,
      cases E,
      case production.concretion { from rfl },
      case production.species {
        from congr_arg production.species (species.rename.restriction _ _),
      }
    },

    case defn : Γ n k l f E D as t ih {
      rcases ih _ (name.ext ρ) with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      simp only [species.rename.invoke],
      simp only [species.rename.choice] at t',
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at t',
      refine ⟨ _, _, defn (lookup.rename ρ f) D _ t', _, _ ⟩,

      rw [label.rename_compose, label.rename_compose, name.mk_apply_rename],
      rw [production.rename_compose, production.rename_compose, name.mk_apply_rename],
    }
  end

  /-- Rename a transition with a basic renaming function. --/
  protected def rename :
    ∀ {Γ Δ f k}
      {A : species ℍ ω Γ} {l : label ℍ Γ k} {E : production ℍ ω Γ k}
      (ρ : name Γ → name Δ)
    , A [f, l]⟶ E
    → (species.rename ρ A) [lookup.rename ρ f, label.rename ρ l]⟶ (production.rename ρ E)
  | Γ Δ f k A l E ρ t := begin
    rcases transition.rename_to ρ t with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
    from t',
  end

  /-- FIXME: Actually prove this. I'm 99% sure it exists, but showing it has
      proved to be rather annoying. -/
  protected constant rename_from :
    ∀ {Γ Δ f k}
      {A : species ℍ ω Γ} {l : label ℍ Δ k} {E : production ℍ ω Δ k}
      (ρ : name Γ → name Δ)
    , species.rename ρ A [f, l]⟶ E
    → Σ' (f' : lookup ℍ ω Γ) (l' : label ℍ Γ k) (E' : production ℍ ω Γ k)
    , pprod (A [f' , l']⟶ E')
            (lookup.rename ρ f' = f ∧ label.rename ρ l' = l ∧ production.rename ρ E' = E)


/-- A transition from a specific species, to any production. -/
@[nolint has_inhabited_instance]
def transition_from {ω Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ) : Type
  := (Σ' k (α : label ℍ Γ k) E, A [ℓ, α]⟶ E)

/-- Construct a new transition_from, wrapping a transition. -/
@[pattern]
def transition_from.mk
    {Γ} {ℓ : lookup ℍ ω Γ} {A : species ℍ ω Γ} {k} {α : label ℍ Γ k} {E} (t : A [ℓ, α]⟶ E)
  : transition_from ℓ A
  := ⟨ k, α, E, t ⟩

/-- Construct a new transition_from with an explicit lookup function, wrapping a
    transition. -/
@[pattern]
def transition_from.mk_with
    {Γ} (ℓ : lookup ℍ ω Γ) {A : species ℍ ω Γ} {k} {α : label ℍ Γ k} {E} (t : A [ℓ, α]⟶ E)
  : transition_from ℓ A
  := ⟨ k, α, E, t ⟩

end transition

end cpi

#lint-

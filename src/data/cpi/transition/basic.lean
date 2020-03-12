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

    (a : name Γ) {n} (b : list (name Γ)) (b_len : list.length b = n) (y : ℕ) (A : species ℍ ω (context.extend y Γ))
    (As : species.choices ℍ ω Γ)
  : transition (Σ# species.whole.cons (a#(b; y)) A As)
               ℓ (#a)
               (production.concretion (#(⟨ b, b_len ⟩; y) A))
| choice₂
    {Γ ℓ}

    (k : ℍ) (A : species ℍ ω Γ) (As : species.choices ℍ ω Γ)
  : transition (Σ# species.whole.cons (τ@k) A As) ℓ τ@'k (production.species A)

| com₁
    {Γ ℓ x y} {A B : species ℍ ω Γ} {a b : name Γ}
    {F : concretion ℍ ω Γ x y} {G : concretion ℍ ω Γ y x}

  : transition A ℓ (#a) (production.concretion F)
  → transition B ℓ (#b) (production.concretion G)
  → transition (A |ₛ B) ℓ τ⟨ a, b ⟩ (production.species (concretion.pseudo_apply F G))

| com₂
    {Γ ℓ} (M : affinity ℍ) {a b : fin M.arity}
    {A B : species ℍ ω (context.extend M.arity Γ)}

    (k : option.is_some (M.f a b))
  : transition A (lookup.rename name.extend ℓ) τ⟨ name.zero a, name.zero b ⟩ (production.species B)
  → transition (ν(M) A) ℓ τ@'(option.get k) (production.species (ν(M) B))

| parL_species
    {Γ ℓ A} B {l : label ℍ Γ kind.species} {E}
  : transition A ℓ l (production.species E) → transition (A |ₛ B) ℓ l (production.species (E |ₛ B))
| parL_concretion
    {Γ ℓ A} B {l : label ℍ Γ kind.concretion} {b y} {E : concretion ℍ ω Γ b y}
  : transition A ℓ l (production.concretion E) → transition (A |ₛ B) ℓ l (production.concretion (E |₁ B))
| parR_species
    {Γ ℓ} A {B} {l : label ℍ Γ kind.species} {E}
  : transition B ℓ l (production.species E) → transition (A |ₛ B) ℓ l (production.species (A |ₛ E))
| parR_concretion
    {Γ ℓ} A {B} {l : label ℍ Γ kind.concretion} {b y} {E : concretion ℍ ω Γ b y}
  : transition B ℓ l (production.concretion E) → transition (A |ₛ B) ℓ l (production.concretion (A |₂ E))

| ν₁_species
    {Γ ℓ} (M : affinity ℍ) {A} {l : label ℍ Γ kind.species} {E}
  : transition A (lookup.rename name.extend ℓ) (label.rename name.extend l) (production.species E)
  → transition (ν(M) A) ℓ l (production.species (ν(M) E))
| ν₁_concretion
    {Γ ℓ} (M : affinity ℍ) {A} {l : label ℍ Γ kind.concretion} {b y} {E : concretion ℍ ω _ b y}
  : transition A (lookup.rename name.extend ℓ) (label.rename name.extend l) (production.concretion E)
  → transition (ν(M) A) ℓ l (production.concretion (ν'(M) E))

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
  /-- Rename a transition with a basic renaming function. --/
  protected def rename :
    ∀ {Γ Δ f k}
      {A : species ℍ ω Γ} {l : label ℍ Γ k} {E : production ℍ ω Γ k}
      (ρ : name Γ → name Δ)
    , A [f, l]⟶ E
    → (species.rename ρ A) [lookup.rename ρ f, label.rename ρ l]⟶ (production.rename ρ E)
  | Γ Δ f k A l E ρ t := begin
    induction t generalizing Δ,
    case ξ_choice : Γ ℓ f π A As k l E t ih {
      have t' := ih _ ρ,
      simp only [species.rename.choice, species.rename.cons] at t' ⊢,
      from ξ_choice t',
    },

    case choice₁ : Γ ℓ a n b b_len y A As {
      simp only [ species.rename.choice, species.rename.cons,
                  prefix_expr.ext_communicate, prefix_expr.rename_communicate ],
      from choice₁ (ρ a) (list.map ρ b) _ y _ _,
    },

    case choice₂ : Γ ℓ k A As {
      simp only [species.rename.choice, species.rename.cons],
      from choice₂ k _ _,
    },

    case com₁ : Γ ℓ x y A B a b F G tf tg ihf ihg {
      simp only [species.rename.parallel, production.rename, label.rename, concretion.pseudo_apply.rename],
      have tf' := ihf _ ρ, have tg' := ihg _ ρ,
      from com₁ tf' tg',
    },

    case com₂ : Γ ℓ M a b A B k t ih {
      simp only [species.rename.restriction, production.rename],
      have t' := ih _ (name.ext ρ),
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at t',
      from com₂ M k t',
    },

    case defn : Γ n k l f E D as t ih {
      simp only [species.rename.invoke],
      rw [label.rename_compose, name.mk_apply_rename, ← label.rename_compose],
      rw [production.rename_compose, name.mk_apply_rename, ← production.rename_compose],

      have t' := ih _ (name.ext ρ),
      simp only [species.rename.choice] at t',
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at t',

      from defn (lookup.rename ρ f) D _ t',
    },

    case parL_species : Γ ℓ A B l E t ih {
      simp only [production.rename, species.rename.parallel],
      from parL_species _ (ih _ ρ),
    },

    case parL_concretion : Γ ℓ A B l b y E t ih {
      simp only [production.rename, species.rename.parallel, concretion.rename],
      from parL_concretion _ (ih _ ρ),
    },

    case parR_species : Γ ℓ A B l E t ih {
      simp only [production.rename, species.rename.parallel],
      from parR_species _ (ih _ ρ),
    },

    case parR_concretion : Γ ℓ A B l b y E t ih {
      simp only [production.rename, species.rename.parallel, concretion.rename],
      from parR_concretion _ (ih _ ρ),
    },

    case ν₁_species : Γ ℓ M A l E t ih {
      simp only [production.rename, species.rename.restriction],
      have t' := ih _ (name.ext ρ),
      rw [label.rename_compose, name.ext_extend, ← label.rename_compose] at t',
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at t',

      from ν₁_species M t',
    },

    case ν₁_concretion : Γ ℓ M A l b y E t ih {
      simp only [production.rename, species.rename.restriction, concretion.rename],
      have t' := ih _ (name.ext ρ),
      rw [label.rename_compose, name.ext_extend, ← label.rename_compose] at t',
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at t',

      from ν₁_concretion M t',
    },
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

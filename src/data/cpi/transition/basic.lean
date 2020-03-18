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
    {FG : species ℍ ω Γ} {α : label ℍ Γ kind.species}

  : FG = concretion.pseudo_apply F G
  → α = τ⟨ a, b ⟩
  → transition A ℓ (#a) (production.concretion F)
  → transition B ℓ (#b) (production.concretion G)
  → transition (A |ₛ B) ℓ α (production.species FG)

| com₂
    {Γ ℓ} (M : affinity ℍ) {p : upair (fin M.arity)} {p' : upair (name (context.extend M.arity Γ))}
    {A B : species ℍ ω (context.extend M.arity Γ)}
    (k : ℍ)
  : M.get p = some k
  → p' = p.map name.zero
  → transition A (lookup.rename name.extend ℓ) τ⟨ p' ⟩ (production.species B)
  → transition (ν(M) A) ℓ τ@'k (production.species (ν(M) B))

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
    {Γ ℓ} (M : affinity ℍ) {A} {l : label ℍ Γ kind.species} {l' : label ℍ (context.extend M.arity Γ) kind.species} {E}
  : l' = label.rename name.extend l
  → transition A (lookup.rename name.extend ℓ) l' (production.species E)
  → transition (ν(M) A) ℓ l (production.species (ν(M) E))
| ν₁_concretion
    {Γ ℓ} (M : affinity ℍ) {A} {l : label ℍ Γ kind.concretion} {l' : label ℍ (context.extend M.arity Γ) kind.concretion}
    {b y} {E : concretion ℍ ω _ b y}
  : l' = label.rename name.extend l
  → transition A (lookup.rename name.extend ℓ) l' (production.concretion E)
  → transition (ν(M) A) ℓ l (production.concretion (ν'(M) E))

| defn
    {Γ k n} {α : label ℍ Γ k} (ℓ : lookup ℍ ω Γ)
    (D : reference n ω) (as : vector (name Γ) n)
    (B : species.choices ℍ ω Γ) {E}
  : (B = species.rename (name.mk_apply as) (ℓ n D))
  → transition (Σ# B) ℓ α E
  → transition (species.apply D as) ℓ α E

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

    case com₁ : Γ ℓ x y A B a b F G C α eqlFG eqlα tf tg ihf ihg {
      subst eqlα, subst eqlFG,
      simp only [species.rename.parallel, production.rename, label.rename, concretion.pseudo_apply.rename],
      have tf' := ihf _ ρ, have tg' := ihg _ ρ,
      from com₁ rfl rfl tf' tg',
    },

    case com₂ : Γ ℓ M p p' A B k eqK eqP t ih {
      subst eqP,
      simp only [species.rename.restriction, production.rename],
      have t' := ih _ (name.ext ρ),
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at t',
      simp only [label.rename] at t',
      rw [upair.map_compose, name.ext_zero] at t',
      from com₂ M k eqK rfl t',
    },

    case defn : Γ n k α ℓ D as B E eql t ih {
      simp only [species.rename.invoke],

      have t' := ih _ ρ,
      simp only [species.rename.choice] at t',

      suffices : cpi.species.rename ρ B = cpi.species.rename (name.mk_apply (vector.map ρ as)) (lookup.rename ρ ℓ k D),
        from defn (lookup.rename ρ ℓ) D (vector.map ρ as) _ this t',

      simp only [lookup.rename],
      rw [species.rename_compose, ← name.mk_apply_rename, ← species.rename_compose (name.mk_apply as) ρ],
      from congr_arg (species.rename ρ) eql,
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

    case ν₁_species : Γ ℓ M A l l' E eql t ih {
      subst eql,
      simp only [production.rename, species.rename.restriction],
      have t' := ih _ (name.ext ρ),
      rw [label.rename_compose, name.ext_extend, ← label.rename_compose] at t',
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at t',

      from ν₁_species M rfl t',
    },

    case ν₁_concretion : Γ ℓ M A l l' b y E eql t ih {
      subst eql,
      simp only [production.rename, species.rename.restriction, concretion.rename],
      have t' := ih _ (name.ext ρ),
      rw [label.rename_compose, name.ext_extend, ← label.rename_compose] at t',
      rw [lookup.rename_compose, name.ext_extend, ← lookup.rename_compose] at t',

      from ν₁_concretion M rfl t',
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
def transition_from {Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ) : Type
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

instance transition_from.has_repr [has_repr ℍ] {Γ} {ℓ : lookup ℍ ω Γ} {A : species ℍ ω Γ}
  : has_repr (transition.transition_from ℓ A)
  := ⟨ λ ⟨ k, α, E, t ⟩, repr A ++ " [" ++ repr α ++ "]⟶ " ++ repr E ⟩

end transition

end cpi

#lint-

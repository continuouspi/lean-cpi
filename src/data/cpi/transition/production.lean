import data.cpi.concretion data.cpi.transition.label

namespace cpi

variables {ℍ : Type} {ω : context}

/-- The right hand side of a transition, determined by a specific kind. -/
@[derive decidable_eq, nolint has_inhabited_instance]
inductive production (ℍ : Type) (ω : context) (Γ : context) : kind → Type
| species (A : species ℍ ω Γ) : production kind.species
| concretion {b y} (F : concretion ℍ ω Γ b y) : production kind.concretion

@[reducible]
instance production.lift_species {Γ}
  : has_coe (species ℍ ω Γ) (production ℍ ω Γ kind.species) := ⟨ production.species ⟩

@[reducible]
instance production.lift_concretion {Γ} {b y}
  : has_coe (concretion ℍ ω Γ b y) (production ℍ ω Γ kind.concretion) := ⟨ production.concretion ⟩

/-- Map over a production, transforming either the concretion or species inside. -/
def production.map
    {Γ Δ} (s : species ℍ ω Γ → species ℍ ω Δ)
    (c : ∀ {b y}, concretion ℍ ω Γ b y → concretion ℍ ω Δ b y)
  : ∀ {k}, production ℍ ω Γ k → production ℍ ω Δ k
| ._ (production.species A) := s A
| ._ (production.concretion F) := c F

/-- Rename a production. This just wraps renaming for species and concretions. -/
def production.rename
  {Γ Δ} (ρ : name Γ → name Δ)
  : ∀ {k}, production ℍ ω Γ k → production ℍ ω Δ k
| ._ (production.species A) := production.species (species.rename ρ A)
| ._ (production.concretion A) := production.concretion (concretion.rename ρ A)

lemma production.rename_compose {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η)
  : ∀ {k} (E : production ℍ ω Γ k)
  , production.rename σ (production.rename ρ E)
  = production.rename (σ ∘ ρ) E
| ._ (production.species A) := congr_arg _ (species.rename_compose ρ σ A)
| ._ (production.concretion F) := congr_arg _ (concretion.rename_compose ρ σ F)

lemma production.rename_id
  {Γ} : ∀ {k} (E : production ℍ ω Γ k), production.rename id E = E
| ._ (production.species A) := congr_arg _ (species.rename_id A)
| ._ (production.concretion F) := congr_arg _ (concretion.rename_id F)

/-- Equivalence of productions. This just wraps equivalence of species and
    concretions. -/
inductive production.equiv [∀ Γ, setoid (species ℍ ω Γ)] [∀ Γ b y, setoid (concretion ℍ ω Γ b y)] {Γ} :
  ∀ {k : kind}, production ℍ ω Γ k → production ℍ ω Γ k → Prop
| species {A B : species ℍ ω Γ}                 : A ≈ B → @production.equiv kind.species A B
| concretion {b y} {F G : concretion ℍ ω Γ b y} : F ≈ G → @production.equiv kind.concretion F G

namespace production
  variables [∀ Γ, setoid (cpi.species ℍ ω Γ)] [∀ Γ b y, setoid (cpi.concretion ℍ ω Γ b y)]

  lemma equiv.refl {Γ} : ∀ {k : kind} (E : production ℍ ω Γ k), equiv E E
  | ._ (species A) := equiv.species (refl A)
  | ._ (concretion F) := equiv.concretion (refl F)

  lemma equiv.symm {Γ} : ∀ {k : kind} (E F : production ℍ ω Γ k), equiv E F → equiv F E
  | ._ ._ ._ (equiv.species eq) := equiv.species (symm eq)
  | ._ ._ ._ (equiv.concretion eq) := equiv.concretion (symm eq)

  lemma equiv.trans {Γ} : ∀ {k : kind} (E F G : production ℍ ω Γ k), equiv E F → equiv F G → equiv E G
  | ._ ._ ._ ._ (equiv.species ef) (equiv.species fg) := equiv.species (trans ef fg)
  | ._ ._ ._ ._ (equiv.concretion ef) (equiv.concretion fg) := equiv.concretion (trans ef fg)

  instance {Γ} {k} : is_equiv (production ℍ ω Γ k) equiv :=
    { refl := equiv.refl, symm := equiv.symm, trans := equiv.trans }
  instance {Γ} {k} : is_refl (production ℍ ω Γ k) equiv := ⟨ equiv.refl ⟩
  instance {Γ} {k} : setoid (production ℍ ω Γ k) :=
    ⟨ equiv, ⟨ equiv.refl, equiv.symm, equiv.trans ⟩ ⟩
  instance setoid.is_equiv {Γ} {k} : is_equiv (production ℍ ω Γ k) has_equiv.equiv :=
    production.is_equiv
end production

section equivalence
variables [∀ Γ, setoid (cpi.species ℍ ω Γ)] [∀ Γ b y, setoid (cpi.concretion ℍ ω Γ b y)]

lemma production.equiv.unwrap_s :
  ∀ {Γ} {A B : species ℍ ω Γ}, production.species A ≈ production.species B → A ≈ B
| Γ A B (production.equiv.species eq) := eq

/-- If two concretions are equivalent under a production, cast one to the type
    of the other. -/
def production.cast_c :
  ∀ {Γ} {a b x y} {F : concretion ℍ ω Γ a x} {G : concretion ℍ ω Γ b y}
  , production.concretion F ≈ production.concretion G
  → concretion ℍ ω Γ a x
| Γ a b x y F G eq := cast (by { cases eq, from rfl }) G

/-- An alternative to 'cast_c', which casts some other concretion of the same
    type. -/
def production.cast_with_c :
  ∀ {Γ} {a b x y} {F : concretion ℍ ω Γ a x} {G G' : concretion ℍ ω Γ b y}
  , production.concretion F ≈ production.concretion G
  → concretion ℍ ω Γ a x
| Γ a b x y F G G' eq := cast (by { cases eq, from rfl }) G' -- TODO: Remove this?

lemma production.cast_c.equiv :
  ∀ {Γ} {a b x y} {F : concretion ℍ ω Γ a x} {G : concretion ℍ ω Γ b y}
    (eq : production.concretion F ≈ production.concretion G)
  , F ≈ production.cast_c eq
| Γ a b x y F G (production.equiv.concretion eq) := eq

lemma production.cast_c.eq :
  ∀ {Γ} {a b x y} {F : concretion ℍ ω Γ a x} {G : concretion ℍ ω Γ b y}
    (eq : production.concretion F ≈ production.concretion G)
  , production.concretion G = production.concretion (production.cast_c eq)
| Γ a b x y F G (production.equiv.concretion eq) := rfl

lemma production.equiv.map {Γ Δ} :
  ∀ {k : kind}
    {s : species ℍ ω Γ → species ℍ ω Δ}
    {c : ∀ {b y}, concretion ℍ ω Γ b y → concretion ℍ ω Δ b y}

    {E F : production ℍ ω Γ k}
  , (∀ {A B : species ℍ ω Γ}, A ≈ B → s A ≈ s B)
  → (∀ {b y} {F G : concretion ℍ ω Γ b y}, F ≈ G → c F ≈ c G)
  → E ≈ F
  → production.map @s @c E ≈ production.map @s @c F
| ._ s c ._ ._ ms mc (production.equiv.species eq) := production.equiv.species (ms eq)
| ._ s c ._ ._ ms mc (production.equiv.concretion eq) := production.equiv.concretion (mc eq)

lemma production.equiv.map_over {Γ Δ} :
  ∀ {k : kind}
    {s s' : species ℍ ω Γ → species ℍ ω Δ}
    {c c' : ∀ {b y}, concretion ℍ ω Γ b y → concretion ℍ ω Δ b y}

    (ms : ∀ (A : species ℍ ω Γ), s A ≈ s' A)
    (mc : ∀ {b y} (F : concretion ℍ ω Γ b y), c F ≈ c' F)
    (E : production ℍ ω Γ k)
  , production.map @s @c E ≈ production.map @s' @c' E
| ._ s s' c c' ms mc (production.species A) := production.equiv.species (ms A)
| ._ s s' c c' ms mc (production.concretion F) := production.equiv.concretion (mc F)
end equivalence

section
  open_locale congruence

  lemma production.equiv.parallel_nil {Γ} :
    ∀ {k : kind} (E : production ℍ ω Γ k)
    , production.map (λ x, x |ₛ nil) (λ _ _ x, x |₁ nil) E ≈ E
  | ._ (production.species _) := production.equiv.species species.equiv.parallel_nil₁
  | ._ (production.concretion _) := production.equiv.concretion concretion.equiv.parallel_nil
end

@[simp]
lemma production.map_compose {Γ Δ η} {k : kind}
    (s  : species ℍ ω Γ → species ℍ ω Δ)
    (s' : species ℍ ω Δ → species ℍ ω η)
    (c  : ∀ {b y}, concretion ℍ ω Γ b y → concretion ℍ ω Δ b y)
    (c' : ∀ {b y}, concretion ℍ ω Δ b y → concretion ℍ ω η b y)
    (E : production ℍ ω Γ k)
  : production.map s' @c' (production.map s @c E)
  = production.map (λ x, s' (s x)) (λ _ _ x, c' (c x)) E
:= by { cases E; repeat { simp only [production.map], unfold_coes } }

end cpi

#lint-

import data.cpi.concretion data.cpi.transition.label

namespace cpi

variables {ℍ : Type} {ω : context}

/-- The right hand side of a transition, determined by a specific kind. -/
@[derive decidable_eq, nolint has_inhabited_instance]
inductive production (ℍ : Type) (ω : context) (Γ : context) : kind → Type
| species (A : species ℍ ω Γ) : production kind.species
| concretion {b y} (F : concretion ℍ ω Γ b y) : production kind.concretion

instance production.has_repr [has_repr ℍ] {Γ k} : has_repr (production ℍ ω Γ k) :=
  ⟨ λ x, by from production.rec_on x repr (λ _ _ x, repr x), ⟩

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
| species {A B : species ℍ ω Γ}
  : A ≈ B → production.equiv (production.species A) (production.species B)
| concretion {b y} {F G : concretion ℍ ω Γ b y}
  : F ≈ G → production.equiv (production.concretion F) (production.concretion G)

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

lemma production.equiv.arity :
  ∀ {Γ} {a b x y} {F : concretion ℍ ω Γ a x} {G : concretion ℍ ω Γ b y}
  , production.concretion F ≈ production.concretion G
  → a = b ∧ x = y
| Γ a b x y F G (production.equiv.concretion eq) := ⟨ rfl, rfl ⟩

lemma production.equiv.unwrap_c :
  ∀ {Γ} {b y} {F : concretion ℍ ω Γ b y} {G : concretion ℍ ω Γ b y}
  , production.concretion F ≈ production.concretion G
  → F ≈ G
| Γ b y F G (production.equiv.concretion eq) := eq

end equivalence

end cpi

#lint-

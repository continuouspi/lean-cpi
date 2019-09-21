import data.cpi.concretion

namespace cpi

/-- The kind of a production, either a species or concretion-/
inductive kind
| species
| concretion

/-- The right hand side of a transition, determined by a specific kind. -/
inductive production (Γ : context) : kind → Type
| species (A : species Γ) : production kind.species
| concretion {b y} (F : concretion Γ b y) : production kind.concretion

@[reducible]
instance production.lift_species {Γ}
  : has_coe (species Γ) (production Γ kind.species) := ⟨ production.species ⟩

@[reducible]
instance production.lift_concretion {Γ} {b y}
  : has_coe (concretion Γ b y) (production Γ kind.concretion) := ⟨ production.concretion ⟩

def production.map {Γ Δ} (s : species Γ → species Δ) (c : ∀ {b y}, concretion Γ b y → concretion Δ b y)
  : ∀ {k}, production Γ k → production Δ k
| ._ (production.species A) := s A
| ._ (production.concretion F) := c F

inductive production.equiv {Γ : context} : ∀ {k : kind}, production Γ k → production Γ k → Prop
| species {A B : species Γ}                 : A ≈ B → @production.equiv kind.species A B
| concretion {b y} {F G : concretion Γ b y} : F ≈ G → @production.equiv kind.concretion F G

namespace production
  def equiv.refl {Γ : context} : ∀ {k : kind} (E : production Γ k), equiv E E
  | ._ (species A) := equiv.species (refl A)
  | ._ (concretion F) := equiv.concretion (refl F)

  def equiv.symm {Γ : context} : ∀ {k : kind} (E F : production Γ k), equiv E F → equiv F E
  | ._ ._ ._ (equiv.species eq) := equiv.species (symm eq)
  | ._ ._ ._ (equiv.concretion eq) := equiv.concretion (symm eq)

  def equiv.trans {Γ : context} : ∀ {k : kind} (E F G : production Γ k), equiv E F → equiv F G → equiv E G
  | ._ ._ ._ ._ (equiv.species ef) (equiv.species fg) := equiv.species (trans ef fg)
  | ._ ._ ._ ._ (equiv.concretion ef) (equiv.concretion fg) := equiv.concretion (trans ef fg)

  instance {Γ} {k} : is_equiv (production Γ k) equiv :=
    { refl := equiv.refl, symm := equiv.symm, trans := equiv.trans }
  instance {Γ} {k} : is_refl (production Γ k) equiv := ⟨ equiv.refl ⟩
  instance {Γ} {k} : setoid (production Γ k) :=
    ⟨ equiv, ⟨ equiv.refl, equiv.symm, equiv.trans ⟩ ⟩
  instance setoid.is_equiv {Γ} {k} : is_equiv (production Γ k) has_equiv.equiv :=
    production.is_equiv
end production

/-- A transition from a species to some production of a given kind. -/
inductive label : context → kind → Type
/- From a species to a concretion. Sends $b$ values on channel $a$ and evolves
   into whatever species the concretion applies, substituting $y$ variables
   with the values received. -/
| apply {Γ} (a : name Γ) : label Γ kind.concretion

/- Evolution from one species to another species without any other interaction,
   at a specific rate. -/
| spontanious {Γ} (rate : ℝ≥0) : label Γ kind.species

/- Evolution from one species to another, with a rate determined by an affinity
   network. This is converted into a spontanious interaction when the names
   refer to a global affinity network. -/
| of_affinity {Γ} (a : name Γ) (b : name Γ) : label Γ kind.species

notation `#`:max a:max := label.apply a
notation `τ@'`:max k:max  := label.spontanious k
notation `τ⟨ `:max a `, ` b ` ⟩`:max := label.of_affinity a b

def label.replace {Γ Δ} (ρ : name Γ → name Δ) : ∀ {k}, label Γ k → label Δ k
| ._ #a := # (ρ a)
| ._ τ@'k := τ@'k
| ._ τ⟨ a, b ⟩ := τ⟨ ρ a, ρ b ⟩

inductive transition : Π {Γ} {k}, species Γ → label Γ k → production Γ k → Type

/- Additional transition to project project into where our choiceₙ rules apply. -/
| ξ_choice
    {Γ} {f} {π : prefix_expr Γ f} {A : species (f Γ)} {As : species.choices Γ}
    {k} {l : label Γ k} {E : production Γ k}

  : transition (species.choice As) l E
  → transition (species.choice (species.choices.cons π A As)) l E

| choice₁
    {Γ}

    (a : name Γ) (b : list (name Γ)) (y : ℕ) (A : species (context.extend y Γ))
    (As : species.choices Γ)
  : transition (species.choice (species.choices.cons (a#(b; y)) A As))
               (label.apply a)
               (#(⟨ b, rfl ⟩; y) A)
| choice₂
    {Γ}

    (k : ℝ≥0) (A : species Γ) (As : species.choices Γ)
  : transition (species.choice (species.choices.cons (τ@k) A As)) τ@'k A

| com₁
    {Γ} {x y} {A B : species Γ} {a b : name Γ}
    {F : concretion Γ x y} {G : concretion Γ y x}

  : transition A (label.apply a) F
  → transition B (label.apply b) G
  → transition (A |ₛ B) τ⟨ a, b ⟩ (concretion.pseudo_apply F G)

| com₂
    {Γ} (M : affinity) {a b : fin M.arity}
    {A B : species (context.extend M.arity Γ)}

    (k : option.is_some (M.f a b))
  : transition A τ⟨ name.zero a, name.zero b ⟩ B
  → transition (ν(M) A) τ@'(option.get k) (ν(M) B)

| parₗ
    {Γ} {A : species Γ} (B : species Γ)
    {k} {l : label Γ k} {E}

  : transition A l E
  → transition (A |ₛ B) l (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E)
| parᵣ
    {Γ} (A : species Γ) {B : species Γ}
    {k} {l : label Γ k} {E}

  : transition B l E
  → transition (A |ₛ B) l (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E)

| ν₁
    {Γ} (M : affinity) {A : species (context.extend M.arity Γ)}
    {k} {l : label Γ k} {E : production (context.extend M.arity Γ) k}

  : transition A (label.replace name.extend l) E
  → transition (ν(M) A) l (production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E)

notation A `[`:max l `]⟶ ` E:max := transition A l E

-- /-- Map a transition from one species to another equivalent one. -/
-- def convert :
--   ∀ {Γ} {A : species Γ} (B : species Γ) {k} {l : label Γ k} {E : production Γ k}
--   , A [l]⟶ E → Σ' (E' : production Γ k) (eq : E ≈ E'), B [l]⟶ E'
--   := sorry

end cpi

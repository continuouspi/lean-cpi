import data.cpi.concretion

namespace cpi

variable {ω : context}

/-- The kind of a production, either a species or concretion-/
inductive kind
| species
| concretion

/-- The right hand side of a transition, determined by a specific kind. -/
inductive production (ω : context) (Γ : context) : kind → Type
| species (A : species ω Γ) : production kind.species
| concretion {b y} (F : concretion ω Γ b y) : production kind.concretion

@[reducible]
instance production.lift_species {Γ}
  : has_coe (species ω Γ) (production ω Γ kind.species) := ⟨ production.species ⟩

@[reducible]
instance production.lift_concretion {Γ} {b y}
  : has_coe (concretion ω Γ b y) (production ω Γ kind.concretion) := ⟨ production.concretion ⟩

def production.map
    {Γ Δ} (s : species ω Γ → species ω Δ)
    (c : ∀ {b y}, concretion ω Γ b y → concretion ω Δ b y)
  : ∀ {k}, production ω Γ k → production ω Δ k
| ._ (production.species A) := s A
| ._ (production.concretion F) := c F

inductive production.equiv {Γ} :
  ∀ {k : kind}, production ω Γ k → production ω Γ k → Prop
| species {A B : species ω Γ}                 : A ≈ B → @production.equiv kind.species A B
| concretion {b y} {F G : concretion ω Γ b y} : F ≈ G → @production.equiv kind.concretion F G

namespace production
  def equiv.refl {Γ} : ∀ {k : kind} (E : production ω Γ k), equiv E E
  | ._ (species A) := equiv.species (refl A)
  | ._ (concretion F) := equiv.concretion (refl F)

  def equiv.symm {Γ} : ∀ {k : kind} (E F : production ω Γ k), equiv E F → equiv F E
  | ._ ._ ._ (equiv.species eq) := equiv.species (symm eq)
  | ._ ._ ._ (equiv.concretion eq) := equiv.concretion (symm eq)

  def equiv.trans {Γ} : ∀ {k : kind} (E F G : production ω Γ k), equiv E F → equiv F G → equiv E G
  | ._ ._ ._ ._ (equiv.species ef) (equiv.species fg) := equiv.species (trans ef fg)
  | ._ ._ ._ ._ (equiv.concretion ef) (equiv.concretion fg) := equiv.concretion (trans ef fg)

  instance {Γ} {k} : is_equiv (production ω Γ k) equiv :=
    { refl := equiv.refl, symm := equiv.symm, trans := equiv.trans }
  instance {Γ} {k} : is_refl (production ω Γ k) equiv := ⟨ equiv.refl ⟩
  instance {Γ} {k} : setoid (production ω Γ k) :=
    ⟨ equiv, ⟨ equiv.refl, equiv.symm, equiv.trans ⟩ ⟩
  instance setoid.is_equiv {Γ} {k} : is_equiv (production ω Γ k) has_equiv.equiv :=
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

inductive transition : Π {Γ} {k}, species ω Γ → label Γ k → production ω Γ k → Type

/- Additional transition to project project into where our choiceₙ rules apply. -/
| ξ_choice
    {Γ} {f} {π : prefix_expr Γ f} {A : species ω (f Γ)} {As : species.choices ω Γ}
    {k} {l : label Γ k} {E : production ω Γ k}

  : transition (Σ# As) l E
  → transition (Σ# species.whole.cons π A As) l E

| choice₁
    {Γ}

    (a : name Γ) (b : list (name Γ)) (y : ℕ) (A : species ω (context.extend y Γ))
    (As : species.choices ω Γ)
  : transition (Σ# species.whole.cons (a#(b; y)) A As)
               (label.apply a)
               (#(⟨ b, rfl ⟩; y) A)
| choice₂
    {Γ}

    (k : ℝ≥0) (A : species ω Γ) (As : species.choices ω Γ)
  : transition (Σ# species.whole.cons (τ@k) A As) τ@'k A

| com₁
    {Γ} {x y} {A B : species ω Γ} {a b : name Γ}
    {F : concretion ω Γ x y} {G : concretion ω Γ y x}

  : transition A (label.apply a) F
  → transition B (label.apply b) G
  → transition (A |ₛ B) τ⟨ a, b ⟩ (concretion.pseudo_apply F G)

| com₂
    {Γ} (M : affinity) {a b : fin M.arity}
    {A B : species ω (context.extend M.arity Γ)}

    (k : option.is_some (M.f a b))
  : transition A τ⟨ name.zero a, name.zero b ⟩ B
  → transition (ν(M) A) τ@'(option.get k) (ν(M) B)

| parₗ
    {Γ} {A : species ω Γ} (B : species ω Γ)
    {k} {l : label Γ k} {E}

  : transition A l E
  → transition (A |ₛ B) l (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E)
| parᵣ
    {Γ} (A : species ω Γ) {B : species ω Γ}
    {k} {l : label Γ k} {E}

  : transition B l E
  → transition (A |ₛ B) l (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E)

| ν₁
    {Γ} (M : affinity) {A : species ω (context.extend M.arity Γ)}
    {k} {l : label Γ k} {E : production ω (context.extend M.arity Γ) k}

  : transition A (label.replace name.extend l) E
  → transition (ν(M) A) l (production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E)


| defn
    {Γ} {n} {l : label (context.extend n Γ) kind.species}
    {f : ∀ {n}, reference n ω → species ω (context.extend n Γ)}

    (B E : species ω (context.extend n Γ))
    (D : reference n ω) (as : vector (name Γ) n)
    {eq : f D = B}
  : transition B l E
  → transition
      (species.apply D as)
      (label.replace (name.mk_apply as) l)
      (species.rename (name.mk_apply as) E)

notation A `[`:max l `]⟶ ` E:max := transition A l E

/-- Map a transition from one species to another equivalent one. -/
constant φ_convert :
  ∀ {Γ} {A : species ω Γ} (B : species ω Γ) {k} {l : label Γ k} {E : production ω Γ k}
  , A [l]⟶ E → Σ' (E' : production ω Γ k) (eq : E ≈ E'), B [l]⟶ E'

end cpi

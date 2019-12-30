import data.cpi.concretion data.upair

namespace cpi

variables {ℍ : Type} {ω : context}

/-- The kind of a production, either a species or concretion-/
@[derive decidable_eq]
inductive kind
| species
| concretion

/-- The right hand side of a transition, determined by a specific kind. -/
@[derive decidable_eq]
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
inductive production.equiv {Γ} :
  ∀ {k : kind}, production ℍ ω Γ k → production ℍ ω Γ k → Prop
| species {A B : species ℍ ω Γ}                 : A ≈ B → @production.equiv kind.species A B
| concretion {b y} {F G : concretion ℍ ω Γ b y} : F ≈ G → @production.equiv kind.concretion F G

namespace production
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

lemma production.equiv.parallel_nil {Γ} :
  ∀ {k : kind} (E : production ℍ ω Γ k)
  , production.map (λ x, x |ₛ nil) (λ _ _ x, x |₁ nil) E ≈ E
| ._ (production.species _) := production.equiv.species species.equiv.parallel_nil₁
| ._ (production.concretion _) := production.equiv.concretion concretion.equiv.parallel_nil

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

/-- A transition from a species to some production of a given kind. -/
@[derive decidable_eq]
inductive label (ℍ : Type) : context → kind → Type
/- From a species to a concretion. Sends $b$ values on channel $a$ and evolves
   into whatever species the concretion applies, substituting $y$ variables
   with the values received. -/
| apply {} {Γ} (a : name Γ) : label Γ kind.concretion

/- Evolution from one species to another species without any other interaction,
   at a specific rate. -/
| spontanious {Γ} (rate : ℍ) : label Γ kind.species

/- Evolution from one species to another, with a rate determined by an affinity
   network. This is converted into a spontanious interaction when the names
   refer to a global affinity network. -/
| of_affinity {} {Γ} (k : upair (name Γ)) : label Γ kind.species

notation `#`:max a:max := label.apply a
notation `τ@'`:max k:max  := label.spontanious k
notation `τ⟨ `:max a `, ` b ` ⟩`:max := label.of_affinity (upair.mk a b)
notation `τ⟨ `:max p ` ⟩`:max := label.of_affinity p

/-- Rename all names within a label. -/
def label.rename {Γ Δ} (ρ : name Γ → name Δ) : ∀ {k}, label ℍ Γ k → label ℍ Δ k
| ._ #a := # (ρ a)
| ._ τ@'k := τ@'k
| ._ τ⟨ ab ⟩ := τ⟨ upair.map ρ ab ⟩

lemma label.rename.inj {Γ Δ} {ρ : name Γ → name Δ} (inj : function.injective ρ)
  : ∀ {k}, function.injective (@label.rename ℍ Γ Δ ρ k)
  | ._ #a #b eq := by { cases inj (label.apply.inj eq), from rfl }
  | ._ τ@'k τ@'j rfl := rfl
  | ._ τ⟨ a ⟩ τ⟨ b ⟩ eq := begin
      cases upair.map.inj inj (label.of_affinity.inj eq),
      from rfl
    end
  | ._ τ@'k τ⟨ _ ⟩ eq := by contradiction
  | ._ τ⟨ _ ⟩ τ@'k eq := by contradiction

lemma label.rename_compose {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η)
  : ∀ {k} (l : label ℍ Γ k)
  , label.rename σ (label.rename ρ l) = label.rename (σ ∘ ρ) l
| ._ #a := rfl
| ._ τ@'k := rfl
| ._ τ⟨ ab ⟩ := by simp only [label.rename, upair.map_compose]

lemma label.rename_id {Γ} : ∀ {k} (l : label ℍ Γ k), label.rename id l = l
| ._ #a := rfl
| ._ τ@'k := rfl
| ._ τ⟨ p ⟩ := congr_arg _ (upair.map_identity p)

/-- A function to look up names within the environment. -/
def lookup (ℍ : Type) (ω Γ : context) := ∀ n, reference n ω → species.choices ℍ ω (context.extend n Γ)

/-- Rename a lookup function, embedding the returned species into another
    context.-/
def lookup.rename {Γ Δ} (ρ : name Γ → name Δ) : lookup ℍ ω Γ → lookup ℍ ω Δ
| f n r := species.rename (name.ext ρ) (f n r)

/-- Rewrite lemma for when lookups get expanded incorrectly. -/
lemma lookup.rename.def {Γ Δ} (ρ : name Γ → name Δ) (ℓ : lookup ℍ ω Γ)
  : (λ n r, species.rename (name.ext ρ) (ℓ n r)) = lookup.rename ρ ℓ
  := rfl

lemma lookup.rename.inj {Γ Δ} {ρ : name Γ → name Δ} (inj : function.injective ρ)
  : function.injective (@lookup.rename ℍ ω Γ Δ ρ)
| x y eq := funext $ λ n, funext $ λ r, begin
  have : species.rename (name.ext ρ) (x n r) = species.rename (name.ext ρ) (y n r)
    := congr_fun (congr_fun eq n) r,
  from species.rename.inj (name.ext.inj inj) this,
end

lemma lookup.rename_compose {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η)
  : ∀ (ℓ : lookup ℍ ω Γ)
  , lookup.rename σ (lookup.rename ρ ℓ) = lookup.rename (σ ∘ ρ) ℓ
| f := funext $ λ n, funext $ λ r, begin
  simp only [lookup.rename, function.comp],
  rw [species.rename_compose (name.ext ρ) (name.ext σ) (f n r), name.ext_comp],
end

/-- A transition from one species to a production. This represents the potential
    for a reaction. The label indicates the kind of reaction (spontantious or
    communicating). -/
inductive transition :
  Π {Γ} {k}
  , species ℍ ω Γ → lookup ℍ ω Γ → label ℍ Γ k → production ℍ ω Γ k
  → Type

/- Additional transition to project project into where our choiceₙ rules apply. -/
| ξ_choice
    {Γ ℓ f} {π : prefix_expr ℍ Γ f} {A : species ℍ ω (context.extend f Γ)} {As : species.choices ℍ ω Γ}
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
  : transition (Σ# species.whole.cons (τ@k) (species.rename name.extend A) As) ℓ τ@'k A

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
                  prefix_expr.rename_communicate,
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
      rw [species.rename_compose, name.ext_extend, ← species.rename_compose],
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

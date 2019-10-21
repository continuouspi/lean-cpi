import data.cpi.concretion data.upair

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

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

def production.rename
  {Γ Δ} (ρ : name Γ → name Δ)
  : ∀ {k}, production ω Γ k → production ω Δ k
| ._ (production.species A) := production.species (species.rename ρ A)
| ._ (production.concretion A) := production.concretion (concretion.rename ρ A)

def production.rename_id
  {Γ} : ∀ {k} (E : production ω Γ k), production.rename id E = E
  | ._ (production.species A) := by { unfold production.rename, rw species.rename_id A }
  | ._ (production.concretion F) := by { unfold production.rename, rw concretion.rename_id F }

def production.free_in : ∀ {Γ} {k} (l : level Γ), production ω Γ k → Prop
| Γ ._ l (production.species A) := l ∈ A
| Γ ._ l (production.concretion F) := l ∈ F

instance production.has_mem {Γ} {k} : has_mem (level Γ) (production ω Γ k) := ⟨ production.free_in ⟩

inductive production.equiv {Γ} :
  ∀ {k : kind}, production ω Γ k → production ω Γ k → Prop
| species {A B : species ω Γ}                 : A ≈ B → @production.equiv kind.species A B
| concretion {b y} {F G : concretion ω Γ b y} : F ≈ G → @production.equiv kind.concretion F G

namespace production
  lemma equiv.refl {Γ} : ∀ {k : kind} (E : production ω Γ k), equiv E E
  | ._ (species A) := equiv.species (refl A)
  | ._ (concretion F) := equiv.concretion (refl F)

  lemma equiv.symm {Γ} : ∀ {k : kind} (E F : production ω Γ k), equiv E F → equiv F E
  | ._ ._ ._ (equiv.species eq) := equiv.species (symm eq)
  | ._ ._ ._ (equiv.concretion eq) := equiv.concretion (symm eq)

  lemma equiv.trans {Γ} : ∀ {k : kind} (E F G : production ω Γ k), equiv E F → equiv F G → equiv E G
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

lemma production.equiv.map {Γ Δ} :
  ∀ {k : kind}
    {s : species ω Γ → species ω Δ}
    {c : ∀ {b y}, concretion ω Γ b y → concretion ω Δ b y}

    {E F : production ω Γ k}
  , (∀ {A B : species ω Γ}, A ≈ B → s A ≈ s B)
  → (∀ {b y} {F G : concretion ω Γ b y}, F ≈ G → c F ≈ c G)
  → E ≈ F
  → production.map @s @c E ≈ production.map @s @c F
| ._ s c ._ ._ ms mc (production.equiv.species eq) := production.equiv.species (ms eq)
| ._ s c ._ ._ ms mc (production.equiv.concretion eq) := production.equiv.concretion (mc eq)

lemma production.equiv.map_over {Γ Δ} :
  ∀ {k : kind}
    {s s' : species ω Γ → species ω Δ}
    {c c' : ∀ {b y}, concretion ω Γ b y → concretion ω Δ b y}

    (ms : ∀ (A : species ω Γ), s A ≈ s' A)
    (mc : ∀ {b y} (F : concretion ω Γ b y), c F ≈ c' F)
    (E : production ω Γ k)
  , production.map @s @c E ≈ production.map @s' @c' E
| ._ s s' c c' ms mc (production.species A) := production.equiv.species (ms A)
| ._ s s' c c' ms mc (production.concretion F) := production.equiv.concretion (mc F)

lemma production.equiv.parallel_nil {Γ} :
  ∀ {k : kind} (E : production ω Γ k)
  , production.map (λ x, x |ₛ nil) (λ _ _ x, x |₁ nil) E ≈ E
| ._ (production.species _) := production.equiv.species species.equiv.parallel_nil₁
| ._ (production.concretion _) := production.equiv.concretion concretion.equiv.parallel_nil

@[simp]
lemma production.map_compose {Γ Δ η} {k : kind}
    (s  : species ω Γ → species ω Δ)
    (s' : species ω Δ → species ω η)
    (c  : ∀ {b y}, concretion ω Γ b y → concretion ω Δ b y)
    (c' : ∀ {b y}, concretion ω Δ b y → concretion ω η b y)
    (E : production ω Γ k)
  : production.map s' @c' (production.map s @c E)
  = production.map (λ x, s' (s x)) (λ _ _ x, c' (c x)) E
:= by { cases E; repeat { simp only [production.map], unfold_coes } }

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
| of_affinity {Γ} (k : upair (name Γ)) : label Γ kind.species

notation `#`:max a:max := label.apply a
notation `τ@'`:max k:max  := label.spontanious k
notation `τ⟨ `:max a `, ` b ` ⟩`:max := label.of_affinity (upair.mk a b)
notation `τ⟨ `:max p ` ⟩`:max := label.of_affinity p

def label.rename {Γ Δ} (ρ : name Γ → name Δ) : ∀ {k}, label Γ k → label Δ k
| ._ #a := # (ρ a)
| ._ τ@'k := τ@'k
| ._ τ⟨ ab ⟩ := τ⟨ upair.map ρ ab ⟩

lemma label.rename.inj {Γ Δ} {ρ : name Γ → name Δ} (inj : function.injective ρ)
  : ∀ {k}, function.injective (@label.rename Γ Δ ρ k)
  | ._ #a #b eq := by { cases inj (label.apply.inj eq), from rfl }
  | ._ τ@'k τ@'j rfl := rfl
  | ._ τ⟨ a ⟩ τ⟨ b ⟩ eq := begin
      cases upair.map.inj inj (label.of_affinity.inj eq),
      from rfl
    end
  | ._ τ@'k τ⟨ _ ⟩ eq := by contradiction
  | ._ τ⟨ _ ⟩ τ@'k eq := by contradiction


lemma label.rename_compose {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η)
  : ∀ {k} (l : label Γ k)
  , label.rename σ (label.rename ρ l) = label.rename (σ ∘ ρ) l
| ._ #a := rfl
| ._ τ@'k := rfl
| ._ τ⟨ ab ⟩ := by simp only [label.rename, upair.map_compose]

lemma label.rename_id {Γ} : ∀ {k} (l : label Γ k), label.rename id l = l
| ._ #a := rfl
| ._ τ@'k := rfl
| ._ τ⟨ p ⟩ := by { unfold label.rename, rw upair.map_identity }

inductive transition : Π {Γ} {k}, species ω Γ → label Γ k → production ω Γ k → Prop

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
               (#a)
               (#(⟨ b, rfl ⟩; y) A)
| choice₂
    {Γ}

    (k : ℝ≥0) (A : species ω Γ) (As : species.choices ω Γ)
  : transition (Σ# species.whole.cons (τ@k) A As) τ@'k A

| com₁
    {Γ} {x y} {A B : species ω Γ} {a b : name Γ}
    {F : concretion ω Γ x y} {G : concretion ω Γ y x}

  : transition A (#a) F
  → transition B (#b) G
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

  : transition A (label.rename name.extend l) E
  → transition (ν(M) A) l (production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E)


| defn
    {Γ} {n} {l : label (context.extend n Γ) kind.species}
    (f : ∀ {n}, reference n ω → species ω (context.extend n Γ))

    (B E : species ω (context.extend n Γ))
    (D : reference n ω) (as : vector (name Γ) n)
    (eq : f D = B)
  : transition B l E
  → transition
      (species.apply D as)
      (label.rename (name.mk_apply as) l)
      (species.rename (name.mk_apply as) E)

notation A ` [`:max l `]⟶ ` E:max := transition A l E

namespace transition
  private lemma congr_arg_heq₂
      {α} {β γ : α → Sort*} (f : ∀ a, β a → γ a)
    : ∀ {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, a₁ = a₂ → b₁ == b₂ → f a₁ b₁ == f a₂ b₂
  | a _ b _ rfl heq.rfl := heq.rfl

  private def rename_env
      {Γ Δ} (ρ : name Γ → name Δ)
      (f : ∀ {n}, reference n ω → species ω (context.extend n Γ))
    : ∀ n, reference n ω → species ω (context.extend n Δ)
  | n r := species.rename (name.ext ρ) (f r)

  protected lemma rename_to :
    ∀ {Γ Δ} {k}
      {A : species ω Γ} {l : label Γ k} {E : production ω Γ k}
      (ρ : name Γ → name Δ)
    , A [l]⟶ E
    → ∃ (l' : label Δ k) (E' : production ω Δ k)
    , (species.rename ρ A) [l']⟶ E'
    ∧ label.rename ρ l = l'
    ∧ production.rename ρ E = E'
  | Γ Δ k A l E ρ t := begin
    induction t generalizing Δ,

    case ξ_choice : Γ f π A As k l E t ih {
      simp only [species.rename.choice, species.rename.cons] at ih ⊢,
      rcases ih _ ρ with ⟨ l', E', t', eql, eqE ⟩,
      from ⟨ l', E', ξ_choice t', eql, eqE ⟩,
    },

    case choice₁ : Γ a b y A As {
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
      refine congr_arg_heq₂ (λ XX YY, @concretion.apply ω Δ XX
          (@subtype.mk (list (name Δ))
            (λ (l : list (name Δ)), list.length l = XX)
            (list.map ρ b)
            YY )
          y
          (species.rename (name.ext ρ) A)) (symm this) _,
      simp only [list.length_map, iff_self, eq_iff_iff, eq_mpr_heq],
    },

    case choice₂ : Γ k A As {
      simp only [species.rename.choice, species.rename.cons],
      from ⟨ τ@'k, _, choice₂ k (species.rename ρ A) (species.rename ρ As), rfl, rfl ⟩
    },

    case com₁ : Γ x y A B a b F G tf tg ihf ihg {
      simp only [species.rename.parallel],
      rcases ihf _ ρ with ⟨ _, _, tf', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      rcases ihg _ ρ with ⟨ _, _, tg', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from ⟨ τ⟨ ρ a, ρ b ⟩, _, com₁ tf' tg', rfl,
             congr_arg production.species (concretion.pseudo_apply.rename ρ F G) ⟩
    },

    case com₂ : Γ M a b A B k t ih {
      simp only [species.rename.restriction],
      rcases ih _ (name.ext ρ) with ⟨ _, _, tf', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from ⟨ _, _, com₂ M k tf', rfl,
             congr_arg production.species (species.rename.restriction M _) ⟩
    },

    case parₗ : Γ A B k l E t ih {
      simp only [species.rename.parallel],
      rcases ih _ ρ with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      refine ⟨ label.rename ρ l, _, parₗ _ t', rfl, _ ⟩,
      cases E,
      case production.concretion { from rfl },
      case production.species {
        from congr_arg production.species (species.rename.parallel _ _),
      }
    },

    case parᵣ : Γ A B k l E t ih {
      simp only [species.rename.parallel],
      rcases ih _ ρ with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      refine ⟨ label.rename ρ l, _, parᵣ _ t', rfl, _ ⟩,
      cases E,
      case production.concretion { from rfl },
      case production.species {
        from congr_arg production.species (species.rename.parallel _ _),
      }
    },

    case ν₁ : Γ M A k l E t ih {
      simp only [species.rename.restriction],
      rcases ih _ (name.ext ρ) with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      rw [label.rename_compose, name.ext_extend, ← label.rename_compose] at t',
      refine ⟨ _, _, ν₁ M t', rfl, _ ⟩,
      cases E,
      case production.concretion { from rfl },
      case production.species {
        from congr_arg production.species (species.rename.restriction _ _),
      }
    },

    case defn : Γ n l f B E D as eq t ih {
      rcases ih _ (name.ext ρ) with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      simp only [species.rename.invoke],
      have eq' : rename_env ρ @f n D = cpi.species.rename (name.ext ρ) B,
        rw ← eq, from rfl,
      refine ⟨ _, _, defn (rename_env ρ @f) _ _ _ _ eq' t', _, _ ⟩,

      rw [label.rename_compose, label.rename_compose, name.mk_apply_rename],
      refine congr_arg production.species _,
      rw [species.rename_compose, species.rename_compose, name.mk_apply_rename],
    }
  end

  protected lemma rename :
    ∀ {Γ Δ} {k}
      {A : species ω Γ} {l : label Γ k} {E : production ω Γ k}
      (ρ : name Γ → name Δ)
    , A [l]⟶ E
    → (species.rename ρ A) [label.rename ρ l]⟶ (production.rename ρ E)
  | Γ Δ k A l E ρ t := begin
    rcases transition.rename_to ρ t with ⟨ _, _, t', ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
    from t',
  end

  /-- FIXME: Actually prove this. I'm 99% sure it's true, but showing it has
      proved to be rather annoying. -/
  protected axiom rename_from :
    ∀ {Γ Δ} {k}
      {A : species ω Γ} {l : label Δ k} {E : production ω Δ k}
      (ρ : name Γ → name Δ)
    , species.rename ρ A [l]⟶ E
    → ∃ (l' : label Γ k) (E' : production ω Γ k)
    , A [l']⟶ E'
    ∧ label.rename ρ l' = l
    ∧ production.rename ρ E' = E


end transition

end cpi

#sanity_check

import data.cpi.transition.basic

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi
namespace transition

variable {ω : context}

open species.equiv (hiding refl trans symm)

private lemma com₁_unpair_con :
  ∀ {Γ} {α : label Γ kind.concretion}
    {A B : species ω Γ}
    {E : production ω Γ kind.concretion}
  , (A |ₛ B) [α]⟶ E
  → ∃ E'
    , (A [α]⟶ E' ∧ production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E' ≈ E)
    ∨ (B [α]⟶ E' ∧ production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E' ≈ E)
| Γ α A B ._ (@parₗ _ _ _ _ _ _ (production.concretion E) t)
  := ⟨ E, or.inl ⟨ t, refl _ ⟩ ⟩
| Γ α A B ._ (@parᵣ _ _ _ _ _ _ (production.concretion E) t)
  := ⟨ E, or.inr ⟨ t, refl _ ⟩ ⟩

private lemma no_rename_zero :
    ∀ {Γ} {n} {a b : fin n} {p : upair (name Γ)}
    , upair.map name.extend p ≠ upair.mk (name.zero a) (name.zero b)
  | Γ n a b p := quot.rec_on p
      (λ ⟨ a₂, b₂ ⟩ eq, by { cases quotient.exact eq; cases h; contradiction })
      (λ _ _ _, rfl)

private lemma on_parallel_assoc₁ :
  ∀ {Γ} {k} {α : label Γ k}
    {A B C : species ω Γ} {E : production ω Γ k}
  , ((A |ₛ B) |ₛ C) [α]⟶ E
  → ∃ E' (eq : E ≈ E'), (A |ₛ B |ₛ C) [α]⟶ E'
| Γ ._ α A B C E (@com₁ _ _ x y _ _ a b F G tf tg) := begin
    rcases com₁_unpair_con tf with ⟨ E', ⟨ t', eqE ⟩ | ⟨ t', eqE ⟩ ⟩;
    cases E' with _ b y F';
    cases eqE with _ _ _ _ _ _ _ eqF,

    -- Using A's transition: push the B into the right
    suffices : concretion.pseudo_apply F G ≈ concretion.pseudo_apply F' (B |₂ G),
      have h := parᵣ B tg,
      refine ⟨ _, production.equiv.species this, com₁ t' h ⟩,
    from calc  concretion.pseudo_apply F G
            ≈ concretion.pseudo_apply (F' |₁ B) G
              : concretion.pseudo_apply.equiv (symm eqF) (refl _)
        ... ≈ concretion.pseudo_apply F' (B |₂ G)
              : concretion.psuedo_apply.parallel_shift F' B G,

    -- Using B's transition: build B|C, and wrap into A.
    suffices : (concretion.pseudo_apply F G) ≈ (A |ₛ concretion.pseudo_apply F' G),
      have h := parᵣ A (com₁ t' tg),
      from ⟨ _, production.equiv.species this, h ⟩,
    from calc  concretion.pseudo_apply F G
            ≈ concretion.pseudo_apply (A |₂ F') G
              : concretion.pseudo_apply.equiv (symm eqF) (refl _)
        ... ≈ (A |ₛ concretion.pseudo_apply F' G)
              : concretion.pseudo_apply.on_parallel₂' A F' G
  end
| Γ k α A B ._ ._ (@parₗ _ _ _ C _ _ E (@com₁ _ _ x y _ _ a b F G tf tg)) :=
  let h := parₗ C tg in
  ⟨ _,
    production.equiv.species (symm (concretion.pseudo_apply.on_parallel₁ _ _ C)),
    com₁ tf h ⟩
| Γ k α A B ._ ._ (parₗ C (@parₗ _ _ _ _ _ _ E t)) := begin
    suffices
      : production.map (λ x, x |ₛ C) (λ _ _ x, x |₁ C)
        (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E)
      ≈ production.map (λ x, x |ₛ B |ₛ C) (λ _ _ x, x |₁ B |ₛ C) E,
      from ⟨ _, this, parₗ (B |ₛ C) t ⟩,

    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, parallel_assoc₁) (λ _ _ _, concretion.equiv.parallel_assoc₁) E,
  end
| Γ k α A B ._ ._ (parₗ C (@parᵣ _ _ _ _ _ _ E t)) := begin
    suffices
      : production.map (λ x, x |ₛ C) (λ _ _ x, x |₁ C)
          (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E)
      ≈ production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x)
          (production.map (λ x, x |ₛ C) (λ _ _ x, x |₁ C) E),
      from ⟨ _, this, parᵣ A (parₗ C t ) ⟩,

    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, equiv.parallel_assoc₁) (λ _ _ _, concretion.equiv.parallel_assoc₂) E,
  end
| Γ k α A B ._ ._ (@parᵣ _ _ _ C _ _ E t) := begin
    suffices
      : production.map (λ x, (A |ₛ B) |ₛ x) (λ _ _ x, (A |ₛ B) |₂ x) E
      ≈ production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x)
          (production.map (λ x, B |ₛ x) (λ _ _ x, B |₂ x) E),
      from ⟨ _, this, parᵣ A (parᵣ B t) ⟩,

    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, equiv.parallel_assoc₁) (λ _ _ _, concretion.equiv.parallel_assoc₃) E,
  end

private lemma on_parallel_symm :
  ∀ {Γ} {k} {α : label Γ k}
    {A B : species ω Γ} {E : production ω Γ k}
  , (A |ₛ B) [α]⟶ E
  → ∃ E' (eq : E ≈ E'), (B |ₛ A) [α]⟶ E'
| Γ ._ ._ A B ._ (@com₁ _ _ x y _ _ a b F G tf tg) := begin
    rw upair.eq a b,
    from ⟨ _, production.equiv.species (concretion.pseudo_apply.symm F G), com₁ tg tf ⟩
  end
| Γ k α A ._ ._ (@parₗ _ _ _ B _ _ E t) := begin
    suffices
      : production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E
      ≈ production.map (λ x, B |ₛ x) (λ _ _ x, B |₂ x) E,
      from ⟨ _, this, parᵣ B t ⟩,
    from production.equiv.map_over
      (λ _, parallel_symm) (λ _ _ _, concretion.equiv.parallel_symm) E,
  end
| Γ k α A ._ ._ (@parᵣ _ _ _ B _ _ E t) := begin
    suffices
        : production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E
        ≈ production.map (λ x, x |ₛ A) (λ _ _ x, x |₁ A) E,
        from ⟨ _, this, parₗ A t ⟩,
    from production.equiv.map_over
      (λ _, parallel_symm) (λ _ _ _, symm concretion.equiv.parallel_symm) E,
  end

private lemma on_parallel_assoc₂ :
  ∀ {Γ} {k} {α : label Γ k}
    {A B C : species ω Γ} {E : production ω Γ k}
  , (A |ₛ B |ₛ C) [α]⟶ E
  → ∃ E' (eq : E ≈ E'), ((A |ₛ B) |ₛ C) [α]⟶ E'
| Γ ._ α A B C E (@com₁ _ _ x y _ _ a b F G tf tg) := begin
    rcases com₁_unpair_con tg with ⟨ E', ⟨ t', eqE ⟩ | ⟨ t', eqE ⟩ ⟩;
    cases E' with _ b y G';
    cases eqE with _ _ _ _ _ _ _ eqG,

    suffices : concretion.pseudo_apply F G ≈ (concretion.pseudo_apply F G' |ₛ C),
      have h := parₗ C (com₁ tf t'),
      from ⟨ _, production.equiv.species this, h ⟩,

    from calc  concretion.pseudo_apply F G
             ≈ concretion.pseudo_apply F (G' |₁ C)
               : concretion.pseudo_apply.equiv (refl _) (symm eqG)
         ... ≈ (concretion.pseudo_apply F G' |ₛ C)
               : concretion.pseudo_apply.on_parallel₁ F G' C,

    suffices : concretion.pseudo_apply F G ≈ concretion.pseudo_apply (F |₁ B) G',
      have h := (parₗ B tf),
      from ⟨ _, production.equiv.species this, com₁ h t' ⟩,

    from calc  concretion.pseudo_apply F G
             ≈ concretion.pseudo_apply F (B |₂ G')
               : concretion.pseudo_apply.equiv (refl _) (symm eqG)
         ... ≈ concretion.pseudo_apply (F |₁ B) G'
               : symm (concretion.psuedo_apply.parallel_shift F B G')
  end
| Γ k α A B C ._ (@parₗ _ _ _ _ _ _ E t) := begin
    suffices
      : production.map (λ x, x |ₛ B |ₛ C) (λ _ _ x, x |₁ B |ₛ C) E
      ≈ production.map (λ x, x |ₛ C) (λ _ _ x, x |₁ C)
          (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E),
      from ⟨ _, this, parₗ C (parₗ B t) ⟩,

    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, equiv.parallel_assoc₂) (λ _ _ F, symm concretion.equiv.parallel_assoc₁) E,
  end
| Γ k α A B C ._ (@parᵣ _ _ _ _ _ _ _ (@com₁ _ _ x y _ _ a b F G tf tg)) :=
  let t' := parᵣ A tf in
  ⟨ _,
    production.equiv.species (symm (concretion.pseudo_apply.on_parallel₂' A F G)),
    com₁ t' tg ⟩
| Γ k α A B C ._ (@parᵣ _ _ _ _ _ _ _ (@parₗ _ _ _ _ _ _ E t)) := begin
    suffices
      : production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x)
          (production.map (λ x, x |ₛ C) (λ _ _ x, x |₁ C) E)
      ≈ production.map (λ x, x |ₛ C) (λ _ _ x, x |₁ C)
          (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E),
      from ⟨ _, this, parₗ C (parᵣ A t) ⟩,

    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, parallel_assoc₂) (λ b y F, symm concretion.equiv.parallel_assoc₂) E
  end
| Γ k α A B C ._ (@parᵣ _ _ _ _ _ _ _ (@parᵣ _ _ _ _ _ _ E t)) := begin
    suffices
      : production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x)
          (production.map (λ x, B |ₛ x) (λ _ _ x, B |₂ x) E)
      ≈ production.map (λ x, (A |ₛ B) |ₛ x) (λ _ _ x, (A |ₛ B) |₂ x) E,
      refine ⟨ _, this, parᵣ (A |ₛ B) t ⟩,

    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, parallel_assoc₂) (λ b y F, symm concretion.equiv.parallel_assoc₃) E,
  end

private lemma on_choice_swap  :
  ∀ {Γ} {k} {α : label Γ k} {f g : context → context}
    {π₁ : prefix_expr Γ f} {π₂ : prefix_expr Γ g}
    {A : species ω (f Γ)} {B : species ω (g Γ)}
    {As : choices ω Γ}
    {E : production ω Γ k}
  , (Σ# whole.cons π₁ A (whole.cons π₂ B As)) [α]⟶ E
  → ∃ E' (eq : E ≈ E')
    , (Σ# whole.cons π₂ B (whole.cons π₁ A As)) [α]⟶ E'
| Γ k α f g π₁ π₂ A B As E t:= begin
  cases t,

  case choice₁ : a b y A As { from ⟨ _, refl _, ξ_choice (choice₁ a b y A As) ⟩ },
  case choice₂ : k A As { from ⟨ _, refl _, ξ_choice (choice₂ k A As) ⟩ },
  case ξ_choice : t {
    cases t,
    case choice₁ : a b y A As { from ⟨ _, refl _, choice₁ a b y A _ ⟩ },
    case choice₂ : k A As { from ⟨ _, refl _, choice₂ k A _ ⟩ },
    case ξ_choice : t { from ⟨ _, refl _, ξ_choice (ξ_choice t) ⟩ },
  },
end


private lemma ν₁_unpair :
  ∀ {Γ} {α : label Γ kind.concretion} {M : affinity}
    {A : species ω (context.extend M.arity Γ)}
    {E : production ω Γ kind.concretion}
  , (ν(M)A) [α]⟶ E
  → ∃ (E' : production ω (context.extend M.arity Γ) kind.concretion)
      (α' : label (context.extend M.arity Γ) kind.concretion)
    , A [α']⟶ E'
    ∧ E = production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E'
    ∧ label.rename name.extend α = α'
| Γ α M A ._ (@ν₁ _ _ _ _ _ _ (production.concretion E) t)
:= ⟨ E, label.rename name.extend α, t, rfl, rfl ⟩

private lemma on_ν_parallel₂ :
  ∀ {Γ} {k} {α : label Γ k} {M : affinity}
    {A : species ω Γ}
    {B : species ω (context.extend (M.arity) Γ)}
    {E : production ω Γ k}
  , (A |ₛ ν(M) B) [α]⟶ E
  → ∃ E' (eq : E ≈ E'), (ν(M) rename name.extend A |ₛ B) [α]⟶ E'
| Γ ._ ._ M A B ._ (@com₁ _ _ x y _ _ a b F G tf tg) := begin
    rcases ν₁_unpair tg with ⟨ E', α', tg', eqE, ⟨ eqα ⟩ ⟩,
    cases E' with _ b' y' G', cases eqE,

    -- Slighty bizzare, but the type annotation allows this to check without
    -- further intermediate steps.
    have tf' := transition.rename name.extend tf,
    have t'
      : (species.rename name.extend A |ₛ B) [label.rename name.extend τ⟨ (upair.mk a b) ⟩]⟶ _
      := com₁ tf' tg',
    refine ⟨ _, _, ν₁ M t' ⟩,
    from production.equiv.species (concretion.pseudo_apply.on_restriction F M G')
  end
| Γ k α M A B ._ (@parₗ _ _ _ _ _ _ E t) := begin
    refine ⟨ _, _, ν₁ M (parₗ B (transition.rename name.extend t)) ⟩,
    simp only [production.map_compose],
    cases E,
    case production.species : E {
      from production.equiv.species (ν_parallel₂ M)
    },
    case production.concretion : b y E {
      from production.equiv.concretion (symm (concretion.equiv.ν_parallel₂ M))
    }
  end
| Γ ._ ._ M ._ B ._ (parᵣ A (@com₂ _ _ _ a b _ E k t)) :=
    let this := parᵣ (species.rename name.extend A) t in
    ⟨ _, production.equiv.species (ν_parallel₂ M), com₂ M k this ⟩
| Γ k ._ M ._ B ._ (parᵣ A (@ν₁ _ _ _ _ _ α E t)) := begin
    have this := parᵣ (species.rename name.extend A) t,
    refine ⟨ _, _, ν₁ M this ⟩,
    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, ν_parallel₂ M) (λ _ _ _, symm (concretion.equiv.ν_parallel₁ M)) E
  end

private lemma on_ν_parallel₁ :
  ∀ {Γ} {k} {α : label Γ k} {M : affinity}
    {A : species ω Γ}
    {B : species ω (context.extend (M.arity) Γ)}
    {E : production ω Γ k}
  , (ν(M) rename name.extend A |ₛ B) [α]⟶ E
  → ∃ E' (eq : E ≈ E'), (A |ₛ ν(M) B) [α]⟶ E'
| Γ k α M A B ._ (@ν₁ _ _ _ _ _ _ E t) := begin
    generalize h₁ : label.rename (@name.extend _ M.arity) α = α',
    generalize h₂ : species.rename (@name.extend _ M.arity) A = A',
    rw [h₁, h₂] at t,

    cases t,
    case com₁ : x y a b F G tf tg {
      subst h₂,
      cases α,
      case label.spontanious { unfold label.rename at h₁, contradiction },

      rcases quot.exists_rep α_k with ⟨ ⟨ a₂, b₂ ⟩, ⟨ _ ⟩ ⟩,

      rcases transition.rename_from name.extend tf with ⟨ lf, F', tf', eqlf, eqF' ⟩,
      cases lf, cases F', unfold label.rename at eqlf,
      cases eqlf, cases eqF',

      have eq' := quotient.exact (label.of_affinity.inj h₁),
      cases eq',
      case or.inl {
        rcases eq' with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
        have tg' : B [label.rename name.extend (#b₂)]⟶ G := tg,
        have this := ν₁ M tg',
        from ⟨ _, production.equiv.species (symm (concretion.pseudo_apply.on_restriction _ M G)),
                 com₁ tf' this ⟩
      },
      case or.inr {
        have : upair.mk b₂ a₂ = quot.mk setoid.r ⟨ a₂, b₂ ⟩ := upair.eq b₂ a₂,
        rw ← this, clear this,

        rcases eq' with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
        have tg' : B [label.rename name.extend (#a₂)]⟶ G := tg,
        have this := ν₁ M tg',
        from ⟨ _, production.equiv.species (symm (concretion.pseudo_apply.on_restriction _ M G)),
                 com₁ tf' this ⟩
      }
    },

    case parₗ : E t' {
      clear t, subst h₁, subst h₂,
      have this := transition.rename_from name.extend t',
      rcases this with ⟨ l₂, E₂ , t₂, eqL, ⟨ _ ⟩ ⟩,
      cases (label.rename.inj (@name.extend.inj _ _) eqL),

      have this := parₗ (ν(M) B) t₂,
      refine ⟨ _, _, this ⟩,

      cases E₂,
      case production.species {
        from production.equiv.species (ν_parallel₁ M),
      },
      case production.concretion {
        from production.equiv.concretion (concretion.equiv.ν_parallel₂ M),
      }
    },
    case parᵣ : E t' {
      subst h₁, subst h₂,
      refine ⟨ _, _, parᵣ _ (ν₁ M t') ⟩,
      simp only [production.map_compose],
      from production.equiv.map_over
        (λ _, ν_parallel₁ M) (λ _ _ _, concretion.equiv.ν_parallel₁ M) E,
    }
  end
| Γ ._ ._ M A B ._ (@com₂ _ _ M' a b _ E k' t) := begin
    -- Abstract some things away to allow us to case-split.
    -- The renaming is strictly not needed, but we get a term explosion as
    -- Lean erroneously inlines rename.
    generalize h₁ : τ⟨ name.zero a, @name.zero Γ _ b ⟩ = α',
    generalize h₂ : production.species E = E',
    generalize h₃ : species.rename (@name.extend _ M.arity) A = A',
    unfold_coes at t, rw [h₁, h₂, h₃] at t,

    cases t,
    case com₁ : x y a' b' F G tf tg {
      subst h₃,
      rcases transition.rename_from name.extend tf with ⟨ l₂, ⟨ E₂ ⟩ , t₂, eqL, eqE ⟩,

      cases l₂, unfold label.rename at eqL; try { contradiction }, cases eqL,
      have eq' := quotient.exact (label.of_affinity.inj h₁),
      cases eq'; cases eq'; contradiction
    },

    case parₗ : E' t' {
      subst h₁, subst h₃, cases E' with E', cases h₂, clear h₂ t,
      rcases transition.rename_from name.extend t' with ⟨ l₂, ⟨ E₂ ⟩ , t₂, eqL, eqE ⟩,

      cases l₂; unfold label.rename at eqL; try { contradiction },
      from false.elim (no_rename_zero (label.of_affinity.inj eqL))
    },

    case parᵣ : E' t' {
      subst h₁, subst h₃, cases E' with E', cases h₂, clear h₂ t,

      have this := parᵣ _ (com₂ M k' t' ),
      refine ⟨ _, production.equiv.species (ν_parallel₁ M), this ⟩,
    },
  end

private lemma on_ν_drop₁ :
  ∀ {Γ} {k} {M : affinity}
    {A : species ω Γ} {α : label Γ k} {E : production ω Γ k}
  , (ν(M) species.rename name.extend A) [α]⟶ E
  → ∃ (E' : production ω Γ k) (eq : E ≈ E'), A [α]⟶ E'
| Γ k M A α E t := begin
  generalize eqA : species.rename (@name.extend _ M.arity) A = A', rw eqA at t,

  cases t,
  case com₂ : a b B k' t' {
    subst eqA,

    rcases transition.rename_from name.extend t' with ⟨ α₂, ⟨ E₂ ⟩ , t₂, eqα, eqE ⟩,
    cases α₂; unfold label.rename at eqα; try { contradiction },
    from false.elim (no_rename_zero (label.of_affinity.inj eqα))
  },
  case ν₁ : E t' {
    subst eqA,

    rcases transition.rename_from name.extend t' with ⟨ α₂, E₂ , t₂, eqα, ⟨ eqE ⟩ ⟩,
    cases label.rename.inj (@name.extend.inj _ _) eqα,

    cases E₂,
    case production.species { from ⟨ _, production.equiv.species (ν_drop₁ M), t₂ ⟩ },
    case production.concretion {
      from ⟨ _, production.equiv.concretion (concretion.equiv.ν_drop M), t₂ ⟩
    }
  }
end

private lemma on_ν_drop₂ :
  ∀ {Γ} {k} {M : affinity}
    {A : species ω Γ} {α : label Γ k} {E : production ω Γ k}
  , A [α]⟶ E
  → ∃ (E' : production ω Γ k) (eq : E ≈ E'), (ν(M) species.rename name.extend A) [α]⟶ E'
  | Γ k M A α E t := begin
    have t' := ν₁ M (transition.rename name.extend t),
    cases E,
    case production.species {
      from ⟨ _, production.equiv.species (ν_drop₂ M), t' ⟩,
    },
    case production.concretion {
      from ⟨ _, production.equiv.concretion (symm (concretion.equiv.ν_drop M)), t' ⟩,
    }
  end

private lemma on_ν_swap₁ :
  ∀ {Γ} {k} {M N : affinity}
    {A : species ω (context.extend (N.arity) (context.extend (M.arity) Γ))}
    {α : label Γ k}
    {E : production ω Γ k}
    , (ν(M) ν(N) A) [α]⟶ E
    → ∃ (E' : production ω Γ k) (eq : E ≈ E')
      , (ν(N) ν(M) species.rename name.swap A) [α]⟶ E'
| Γ k M N A α E₁ t₁ := begin
  cases t₁,

  case ν₁ : E₂ t₂ {
    generalize eqα : label.rename (@name.extend _ M.arity) α = α₂, rw eqα at t₂,
    cases t₂,

    case ν₁ : E₃ t₃ {
      cases eqα, clear t₁ t₂,
      have t' := transition.rename name.swap t₃,

      have : (name.swap ∘ (@name.extend _ N.arity)) ∘ (@name.extend _ M.arity) = name.extend ∘ name.extend,
        apply funext, assume x, unfold function.comp name.swap,
      rw [label.rename_compose, label.rename_compose, this, ← label.rename_compose] at t',

      refine ⟨ _, _, ν₁ N (ν₁ M t') ⟩,
      cases E₃,
      case production.species { from production.equiv.species (ν_swap₁ M N) },
      case production.concretion {
        from production.equiv.concretion (concretion.equiv.ν_swap M N),
      },
    },

    case com₂ : a b B k t₃ {
      cases α; unfold label.rename at eqα; try { contradiction }, cases eqα,
      clear eqα t₁ t₂,

      have t' := transition.rename name.swap t₃,
      unfold label.rename at t', rw upair.map_beta name.swap _ _ at t', unfold name.swap at t',

      have t' :
        (species.rename name.swap A)
        [label.rename name.extend τ⟨ (upair.mk (name.zero a) (name.zero b)) ⟩]⟶
        (production.rename name.swap B),
        unfold label.rename, rw upair.map_beta name.extend _ _, from t',

      have this := ν₁ M t',
      refine ⟨ _, production.equiv.species (ν_swap₁ M N), com₂ N _ this ⟩,
    }
  },

  case com₂ : a b B k t₂ {
    generalize eqB : production.species B = E, unfold_coes at t₂, rw eqB at t₂,
    cases t₂, cases t₂_E, cases eqB,

    have t' := transition.rename name.swap t₂_a,
    have : (ν(M) species.rename name.swap A) [label.rename name.extend τ@'(option.get k)]⟶ ν(M) species.rename name.swap t₂_E_1,
      from com₂ M _ t',
    have this := ν₁ N this,
    from ⟨ _, production.equiv.species (ν_swap₁ M N), this ⟩,
  }
end

private lemma on_ν_swap₂ :
  ∀ {Γ} {k} {M N : affinity}
    {A : species ω (context.extend (N.arity) (context.extend (M.arity) Γ))}
    {α : label Γ k} {E : production ω Γ k}
  , (ν(N) ν(M) species.rename name.swap A) [α]⟶ E
  → ∃ (E' : production ω Γ k) (eq : E ≈ E'), (ν(M) ν(N) A) [α]⟶ E'
| Γ k M N A α E t₁ := begin
  generalize eqA : species.rename name.swap A = A', rw eqA at t₁,
  cases t₁,

  case com₂ : a b B k t₂ {
    generalize eqB : production.species B = E, unfold_coes at t₂, rw eqB at t₂,
    cases t₂, subst eqA, cases t₂_E, cases eqB, clear eqB t₂ t₁,

    have t' := transition.rename name.swap t₂_a,
    have this := com₂ N k t',
    have : (ν(N) A ) [label.rename name.extend τ@'(option.get k)]⟶ ↑ν(N) species.rename name.swap t₂_E_1,
      unfold label.rename,
      rw [species.rename_compose, name.swap_swap, species.rename_id] at this,
      from this,
    refine ⟨ _, _, ν₁ M this ⟩,
    from production.equiv.species (ν_swap₁ N M),
  },

  case ν₁ : E₂ t₂ {
    generalize eqα : label.rename (@name.extend _ N.arity) α = α₂, rw eqα at t₂,
    cases t₂,

    case ν₁ : E₃ t₃ {
      subst eqA, subst eqα, clear t₁ t₂,

      have t' := transition.rename name.swap t₃,
      have : A [label.rename name.extend (label.rename name.extend α)]⟶ _,
        rw [species.rename_compose, name.swap_swap, species.rename_id] at t',
        rw [label.rename_compose, label.rename_compose, name.swap_comp_extend, name.ext_extend, ← label.rename_compose ] at t',
        from t',

      refine ⟨ _, _, ν₁ M (ν₁ N this) ⟩,
      cases E₃,
      case production.species { from production.equiv.species (ν_swap₁ N M) },
      case production.concretion {
        from production.equiv.concretion (concretion.equiv.ν_swap N M)
      },
    },
    case com₂ : a b B k t₃ {
      cases α; unfold label.rename at eqα; try { contradiction }, cases eqα,
      subst eqA, clear t₁ t₂,

      have t' :
        A
        [label.rename name.extend τ⟨ (upair.mk (name.zero a) (name.zero b)) ⟩]⟶
        (production.rename name.swap ↑B),
        have this := transition.rename name.swap t₃,

        unfold label.rename at this ⊢, rw upair.map_beta at this, rw upair.map_beta,
        rw [species.rename_compose, name.swap_swap, species.rename_id] at this,

        from this,

      have this := ν₁ N t',
      from ⟨ _, production.equiv.species (ν_swap₁ N M), com₂ M k this ⟩,
    },
  }
end

theorem equivalent :
  ∀ {Γ} {A : species ω Γ} {B : species ω Γ} {k} {α : label Γ k} {E : production ω Γ k}
  , A ≈ B → A [α]⟶ E
  → ∃ (E' : production ω Γ k) (eq : E ≈ E'), B [α]⟶ E'
| Γ₁ A₁ B₁ k₁ α₁ E₁ equ t₁ := begin
  induction equ generalizing k₁,

  case species.equiv.refl { from ⟨ E₁, refl _, t₁ ⟩ },
  case species.equiv.trans : Γ A B C ab bc ih_ab ih_bc {
    rcases ih_ab _ α₁ E₁ t₁ with ⟨ E₂, eq₂, t₂ ⟩,
    rcases ih_bc _ α₁ E₂ t₂ with ⟨ E₃, eq₃, t₃ ⟩,
    from ⟨ E₃, trans eq₂ eq₃, t₃ ⟩
  },

  case ξ_parallel₁ : Γ A A' B eq ih {
    cases t₁,
    case com₁ : x y a b F G tf tg {
      rcases ih _ (#a) F tf with ⟨ F', equ, tf' ⟩,
      cases F' with _ b y' F', cases equ,
      -- Not sure what's going on here, but I can't destructure this

      from ⟨ concretion.pseudo_apply equ_G G,
             production.equiv.species (concretion.pseudo_apply.equiv equ_a (refl G)),
             com₁ tf' tg ⟩
    },
    case parₗ : E t {
      rcases ih _ α₁ E t with ⟨ E', equ, t' ⟩,
      have eqE
        : (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E)
        ≈ (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E')
        := production.equiv.map
          (λ _ _, ξ_parallel₁) (λ _ _ _ _, concretion.equiv.ξ_parallel₁) equ,

      from ⟨ _, eqE, parₗ B t' ⟩
    },
    case parᵣ : E t {
      have eqE
        : (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E)
        ≈ (production.map (λ x, A' |ₛ x) (λ _ _ x, A' |₂ x) E)
        := production.equiv.map_over
            (λ _, ξ_parallel₁ eq) (λ _ _ _, concretion.equiv.ξ_parallel' eq) E,
      from ⟨ _, eqE, parᵣ A' t ⟩,
    }
  },

  case ξ_parallel₂ : Γ A B B' eq ih {
    cases t₁,
    case com₁ : x y a b F G tf tg {
      rcases ih _ (#b) G tg with ⟨ G', equ, tg' ⟩,
      cases G' with _ b y' G', cases equ,

      from ⟨ concretion.pseudo_apply F equ_G,
             production.equiv.species (concretion.pseudo_apply.equiv (refl F) equ_a),
             com₁ tf tg' ⟩
    },
    case parₗ : E t {
      have eqE
        : (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E)
        ≈ (production.map (λ x, x |ₛ B') (λ _ _ x, x |₁ B') E)
        := production.equiv.map_over
            (λ _, ξ_parallel₂ eq) (λ _ _ _, concretion.equiv.ξ_parallel eq) E,
      from ⟨ _, eqE, parₗ B' t ⟩,
    },
    case parᵣ : E t {
      rcases ih _ α₁ E t with ⟨ E', equ, t' ⟩,
      have eqE
        : (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E)
        ≈ (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E')
        := production.equiv.map
          (λ _ _, ξ_parallel₂) (λ _ _ _ _, concretion.equiv.ξ_parallel₂) equ,
      from ⟨ _, eqE, parᵣ A t' ⟩,
    }
  },

  case ξ_restriction : Γ M A A' eq ih {
    cases t₁,

    case com₂ : a b B defn t {
      rcases ih _ τ⟨ name.zero a, name.zero b ⟩ B t with ⟨ E', equ, t' ⟩,
      cases E' with B', cases equ with _ _ equ,
      from ⟨ _, production.equiv.species (ξ_restriction M equ), com₂ M defn t' ⟩
    },

    case ν₁ : E t {
      rcases ih _ (label.rename name.extend α₁) E t with ⟨ E', equ, t' ⟩,
      have eqE
        : (production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E)
        ≈ (production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E'),
        from production.equiv.map
          (λ _ _, ξ_restriction M) (λ _ _ _ _, concretion.equiv.ξ_restriction M) equ,

      from ⟨ _, eqE, ν₁ M t' ⟩,
    }
  },

  case ξ_choice_here : Γ f π A A' As eq ih {
    cases t₁,
    case ξ_choice : t { refine ⟨ _, refl _, ξ_choice t ⟩ },
    case choice₁ : a b y {
      from ⟨ _, production.equiv.concretion (concretion.equiv.ξ_apply eq), choice₁ a b y A' As ⟩,
    },
    case choice₂ : k { from ⟨ _, production.equiv.species eq, choice₂ k A' As ⟩ },
  },

  case ξ_choice_there : Γ f π A As As' eq ih {
    cases t₁,

    case ξ_choice : t {
      rcases ih _ α₁ E₁ t with ⟨ E', equ, t' ⟩,
      refine ⟨ _, equ, ξ_choice t' ⟩,
    },
    case choice₁ : a b y A As { from ⟨ _, refl _, choice₁ a b y A As' ⟩ },
    case choice₂ : k A As { from ⟨ _, refl _, choice₂ k A As' ⟩ },
  },

  case parallel_nil₁ : Γ A {
    cases t₁,

    -- No such transition for (nil ⟶ _)
    case com₁ : x y a b F G tf tg { cases tg },
    case parᵣ : E t { cases t },
    case parₗ : E t { from ⟨ _, production.equiv.parallel_nil E, t ⟩ },
  },

  case parallel_nil₂ : Γ B {
    from ⟨ _, symm (production.equiv.parallel_nil E₁), parₗ species.nil t₁ ⟩
  },

  case choice_swap { from on_choice_swap t₁ },

  case parallel_assoc₁ { from on_parallel_assoc₁ t₁ },
  case parallel_assoc₂ { from on_parallel_assoc₂ t₁ },

  case parallel_symm { from on_parallel_symm t₁ },

  case ν_parallel₁ { from on_ν_parallel₁ t₁ },
  case ν_parallel₂ { from on_ν_parallel₂ t₁ },
  case ν_drop₁ { from on_ν_drop₁ t₁ },
  case ν_drop₂ { from on_ν_drop₂ t₁ },
  case ν_swap₁ { from on_ν_swap₁ t₁ },
  case ν_swap₂ { from on_ν_swap₂ t₁ },
end

end transition
end cpi

#sanity_check
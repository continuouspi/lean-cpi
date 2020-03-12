import data.cpi.transition.basic

namespace cpi
namespace transition

variables {ℍ : Type} {ω : context}
open_locale congruence

open species.equiv

private def no_rename_zero :
    ∀ {Γ} {n} {a b : fin n} {p : upair (name Γ)}
    , upair.map name.extend p ≠ upair.mk (name.zero a) (name.zero b)
  | Γ n a b p := quot.rec_on p
      (λ ⟨ a₂, b₂ ⟩ eq, by { cases quotient.exact eq; cases h; contradiction })
      (λ _ _ _, rfl)

private def on_parallel_assoc₁ {Γ ℓ} {A B C : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , ((A |ₛ B) |ₛ C) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E'), (A |ₛ B |ₛ C) [ℓ, α]⟶ E'
| k α E (@com₁ _ _ _ _ x y _ _ a b _ G (parL_concretion D tf) tg) :=
  ⟨ _, production.equiv.species (concretion.pseudo_apply.parallel_shift _ B G),
   com₁ tf (parR_concretion _ tg) ⟩
| k α E (@com₁ _ _ _ _ x y _ _ a b _ G (parR_concretion D tf) tg) :=
  ⟨ _, production.equiv.species (concretion.pseudo_apply.on_parallel₂' A _ G),
   parR_species A (com₁ tf tg) ⟩
| k α E (parL_species _ (@com₁ _ _ _ _ x y _ _ a b F G tf tg)) :=
  ⟨ _, production.equiv.species (symm (concretion.pseudo_apply.on_parallel₁ _ _ C)),
   com₁ tf (parL_concretion C tg) ⟩
| k α E (parL_species B (parL_species C t)) :=
  ⟨ _, production.equiv.species parallel_assoc₁, parL_species _ t ⟩
| k α E (parL_concretion B (parL_concretion C t)) :=
  ⟨ _, production.equiv.concretion concretion.equiv.parallel_assoc₁, parL_concretion _ t ⟩
| k α E (parL_species C (parR_species _ t)) :=
  ⟨ _, production.equiv.species equiv.parallel_assoc₁, parR_species _ (parL_species _ t) ⟩
| k α E (parL_concretion C (parR_concretion D t)) :=
  ⟨ _, production.equiv.concretion concretion.equiv.parallel_assoc₂, parR_concretion _ (parL_concretion _ t) ⟩
| k α E (parR_species D t) :=
  ⟨ _, production.equiv.species equiv.parallel_assoc₁, parR_species A (parR_species B t) ⟩
| k α E (parR_concretion D t) :=
  ⟨ _, production.equiv.concretion concretion.equiv.parallel_assoc₃, parR_concretion A (parR_concretion B t) ⟩

private def on_parallel_symm {Γ ℓ} {A B : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , (A |ₛ B) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E'), (B |ₛ A) [ℓ, α]⟶ E'
| ._ ._ ._ (@com₁ _ _ _ _ x y _ _ a b F G tf tg) := begin
    rw upair.eq a b,
    from ⟨ _, production.equiv.species (concretion.pseudo_apply.symm F G), com₁ tg tf ⟩
  end
| k α ._ (parL_species _ t) := ⟨ _, production.equiv.species parallel_symm, parR_species B t ⟩
| k α ._ (parL_concretion _ t) := ⟨ _, production.equiv.concretion concretion.equiv.parallel_symm, parR_concretion B t ⟩
| k α ._ (parR_species _ t) := ⟨ _, production.equiv.species parallel_symm, parL_species A t ⟩
| k α ._ (parR_concretion _ t) := ⟨ _, production.equiv.concretion (symm concretion.equiv.parallel_symm), parL_concretion A t ⟩

/-
private def on_parallel_assoc₂ :
  ∀ {Γ ℓ k} {α : label ℍ Γ k}
    {A B C : species ℍ ω Γ} {E : production ℍ ω Γ k}
  , (A |ₛ B |ₛ C) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E'), ((A |ₛ B) |ₛ C) [ℓ, α]⟶ E'
| Γ f ._ α A B C E (@com₁ _ _ _ _ x y _ _ a b F G tf tg) := begin
    rcases com₁_unpair_con tg with ⟨ E', ⟨ t', eqE ⟩ | ⟨ t', eqE ⟩ ⟩;
    cases E' with _ b y G';
    cases eqE,

    suffices : concretion.pseudo_apply F (G' |₁ C) ≈ (concretion.pseudo_apply F G' |ₛ C),
      have h := parL C (com₁ tf t'),
      from ⟨ _, production.equiv.species this, h ⟩,
    from concretion.pseudo_apply.on_parallel₁ F G' C,

    suffices : concretion.pseudo_apply F (B |₂ G') ≈ concretion.pseudo_apply (F |₁ B) G',
      have h := (parL B tf),
      from ⟨ _, production.equiv.species this, com₁ h t' ⟩,
    from symm (concretion.pseudo_apply.parallel_shift F B G'),
  end
| Γ ℓ k α A B C ._ (@parL _ _ _ _ _ _ _ _ E t) := begin
    suffices
      : production.map (λ x, x |ₛ B |ₛ C) (λ _ _ x, x |₁ B |ₛ C) E
      ≈ production.map (λ x, x |ₛ C) (λ _ _ x, x |₁ C)
          (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E),
      from ⟨ _, this, parL C (parL B t) ⟩,

    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, equiv.parallel_assoc₂) (λ _ _ F, symm concretion.equiv.parallel_assoc₁) E,
  end
| Γ ℓ k α A B C ._ (@parR _ _ _ _ _ _ _ _ _ (@com₁ _ _ _ _ x y _ _ a b F G tf tg)) :=
  let t' := parR A tf in
  ⟨ _,
    production.equiv.species (symm (concretion.pseudo_apply.on_parallel₂' A F G)),
    com₁ t' tg ⟩
| Γ ℓ k α A B C ._ (@parR _ _ _ _ _ _ _ _ _ (@parL _ _ _ _ _ _ _ _ E t)) := begin
    suffices
      : production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x)
          (production.map (λ x, x |ₛ C) (λ _ _ x, x |₁ C) E)
      ≈ production.map (λ x, x |ₛ C) (λ _ _ x, x |₁ C)
          (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E),
      from ⟨ _, this, parL C (parR A t) ⟩,

    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, parallel_assoc₂) (λ b y F, symm concretion.equiv.parallel_assoc₂) E
  end
| Γ ℓ k α A B C ._ (@parR _ _ _ _ _ _ _ _ _ (@parR _ _ _ _ _ _ _ _ E t)) := begin
    suffices
      : production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x)
          (production.map (λ x, B |ₛ x) (λ _ _ x, B |₂ x) E)
      ≈ production.map (λ x, (A |ₛ B) |ₛ x) (λ _ _ x, (A |ₛ B) |₂ x) E,
      refine ⟨ _, this, parR (A |ₛ B) t ⟩,

    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, parallel_assoc₂) (λ b y F, symm concretion.equiv.parallel_assoc₃) E,
  end

private def on_choice_swap  :
  ∀ {Γ ℓ k f g} {α : label ℍ Γ k}
    {π₁ : prefix_expr ℍ Γ f} {π₂ : prefix_expr ℍ Γ g}
    {A : species ℍ ω (f.apply Γ)} {B : species ℍ ω (g.apply Γ)}
    {As : choices ℍ ω Γ}
    {E : production ℍ ω Γ k}
  , (Σ# whole.cons π₁ A (whole.cons π₂ B As)) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E')
    , (Σ# whole.cons π₂ B (whole.cons π₁ A As)) [ℓ, α]⟶ E'
| Γ ℓ k α f g π₁ π₂ A B As E t:= begin
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

private def ν₁_unpair :
  ∀ {Γ ℓ} {α : label ℍ Γ kind.concretion} {M : affinity ℍ}
    {A : species ℍ ω (context.extend M.arity Γ)}
    {E : production ℍ ω Γ kind.concretion}
  , (ν(M)A) [ℓ, α]⟶ E
  → Σ' (E' : production ℍ ω (context.extend M.arity Γ) kind.concretion)
       (α' : label ℍ (context.extend M.arity Γ) kind.concretion)
    , pprod
      (A [lookup.rename name.extend ℓ, α']⟶ E')
      ( E = production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E'
      ∧ label.rename name.extend α = α')
| Γ f α M A ._ (@ν₁ _ _ _ _ _ _ _ _ (production.concretion E) t)
:= ⟨ E, label.rename name.extend α, t, rfl, rfl ⟩

private def on_ν_parallel₂ :
  ∀ {Γ ℓ k} {α : label ℍ Γ k} {M : affinity ℍ}
    {A : species ℍ ω Γ}
    {B : species ℍ ω (context.extend (M.arity) Γ)}
    {E : production ℍ ω Γ k}
  , (A |ₛ ν(M) B) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E'), (ν(M) rename name.extend A |ₛ B) [ℓ, α]⟶ E'
| Γ f ._ ._ M A B ._ (@com₁ _ _ _ _ x y _ _ a b F G tf tg) := begin
    rcases ν₁_unpair tg with ⟨ E', α', tg', eqE, ⟨ eqα ⟩ ⟩,
    cases E' with _ b' y' G', cases eqE,

    -- Slighty bizzare, but the type annotation allows this to check without
    -- further intermediate steps.
    have tf' := transition.rename name.extend tf,
    have t'
      : (species.rename name.extend A |ₛ B) [_, label.rename name.extend τ⟨ (upair.mk a b) ⟩]⟶ _
      := com₁ tf' tg',
    refine ⟨ _, _, ν₁ M t' ⟩,
    from production.equiv.species (concretion.pseudo_apply.on_restriction F M G')
  end
| Γ ℓ k α M A B ._ (@parL _ _ _ _ _ _ _ _ E t) := begin
    refine ⟨ _, _, ν₁ M (parL B (transition.rename name.extend t)) ⟩,
    simp only [production.map_compose],
    cases E,
    case production.species : E {
      from production.equiv.species (ν_parallel₂ M)
    },
    case production.concretion : b y E {
      from production.equiv.concretion (symm (concretion.equiv.ν_parallel₂ M))
    }
  end
| Γ f ._ ._ M ._ B ._ (parR A (@com₂ _ _ _ _ _ a b _ E k t)) :=
    let this := parR (species.rename name.extend A) t in
    ⟨ _, production.equiv.species (ν_parallel₂ M), com₂ M k this ⟩
| Γ ℓ k ._ M ._ B ._ (parR A (@ν₁ _ _ _ _ _ _ _ α E t)) := begin
    have this := parR (species.rename name.extend A) t,
    refine ⟨ _, _, ν₁ M this ⟩,
    simp only [production.map_compose],
    from production.equiv.map_over
      (λ _, ν_parallel₂ M) (λ _ _ _, symm (concretion.equiv.ν_parallel₁ M)) E
  end

private noncomputable def on_ν_parallel₁ :
  ∀ {Γ ℓ k} {α : label ℍ Γ k} {M : affinity ℍ}
    {A : species ℍ ω Γ}
    {B : species ℍ ω (context.extend (M.arity) Γ)}
    {E : production ℍ ω Γ k}
  , (ν(M) rename name.extend A |ₛ B) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E'), (A |ₛ ν(M) B) [ℓ, α]⟶ E'
| Γ ℓ k α M A B ._ (@ν₁ _ _ _ _ _ _ _ _ E t) := begin
    generalize h₁ : label.rename (@name.extend _ M.arity) α = α',
    generalize h₂ : species.rename (@name.extend _ M.arity) A = A',
    rw [h₁, h₂] at t,

    cases t,
    case com₁ : x y a b F G tf tg {
      subst h₂,
      cases α,
      case label.spontanious { unfold label.rename at h₁, contradiction },

      rcases transition.rename_from name.extend tf with ⟨ ℓ', lf, F', tf', eqℓ, eqlf, eqF' ⟩,
      have : ℓ' = ℓ := lookup.rename.inj (@name.extend.inj _ _) eqℓ, subst this,
      cases lf, cases F', unfold label.rename at eqlf,
      cases eqlf, cases eqF',
      simp only [label.rename] at h₁,
      rcases upair.unpair₁ (@name.extend.inj _ _) h₁ with ⟨ b₂, eqB ⟩, cases eqB,

      have eqα : α_k = upair.mk lf_a b₂,
        suffices
          : upair.map (@name.extend _ M.arity) α_k
          = upair.map name.extend (upair.mk lf_a b₂),
          from upair.map.inj (@name.extend.inj _ _) this,
        rw upair.map_beta name.extend,
        from h₁,
      cases eqα,

      have tg' : B [_, label.rename name.extend (#b₂)]⟶ G := tg,
      have this := ν₁ M tg',
      from ⟨ _,
             production.equiv.species (symm (concretion.pseudo_apply.on_restriction _ M G)),
             com₁ tf' this ⟩,
    },

    case parL : E t' {
      subst h₁, subst h₂,
      have this := transition.rename_from name.extend t',
      rcases this with ⟨ ℓ₂, l₂, E₂ , t₂, eqℓ, eqL, ⟨ _ ⟩ ⟩,
      cases (label.rename.inj (@name.extend.inj _ _) eqL),
      have : ℓ₂ = ℓ := lookup.rename.inj (@name.extend.inj _ _) eqℓ, subst this,

      have this := parL (ν(M) B) t₂,
      refine ⟨ _, _, this ⟩,

      cases E₂,
      case production.species {
        from production.equiv.species (ν_parallel₁ M),
      },
      case production.concretion {
        from production.equiv.concretion (concretion.equiv.ν_parallel₂ M),
      }
    },
    case parR : E t' {
      subst h₁, subst h₂,
      refine ⟨ _, _, parR _ (ν₁ M t') ⟩,
      simp only [production.map_compose],
      from production.equiv.map_over
        (λ _, ν_parallel₁ M) (λ _ _ _, concretion.equiv.ν_parallel₁ M) E,
    }
  end
| Γ f ._ ._ M A B ._ (@com₂ _ _ _ _ M' a b _ E k' t) := begin
    -- Abstract some things away to allow us to case-split.
    -- The renaming is strictly not needed, but we get a term explosion as
    -- Lean erroneously inlines rename.
    generalize h₁ : @label.of_affinity ℍ _ (upair.mk (name.zero a) (@name.zero Γ _ b)) = α',
    generalize h₂ : production.species E = E',
    generalize h₃ : species.rename (@name.extend _ M.arity) A = A',
    unfold_coes at t, rw [h₁, h₂, h₃] at t,

    cases t,
    case com₁ : x y a' b' F G tf tg {
      subst h₃,
      rcases transition.rename_from name.extend tf with ⟨ ℓ₂, l₂, ⟨ E₂ ⟩ , t₂, eqℓ, eqL, eqE ⟩,

      cases l₂, unfold label.rename at eqL; try { contradiction }, cases eqL,
      exfalso,
      have eq' := quotient.exact (label.of_affinity.inj h₁),
      cases eq'; cases eq'; contradiction
    },

    case parL : E' t' {
      subst h₁, subst h₃, cases E' with E', cases h₂, clear h₂,
      rcases transition.rename_from name.extend t' with ⟨ ℓ₂, l₂, ⟨ E₂ ⟩ , t₂, eqℓ, eqL, eqE ⟩,

      cases l₂; unfold label.rename at eqL; try { contradiction },
      from false.elim (no_rename_zero (label.of_affinity.inj eqL))
    },

    case parR : E' t' {
      subst h₁, subst h₃, cases E' with E', cases h₂, clear h₂,

      have this := parR _ (com₂ M k' t' ),
      refine ⟨ _, production.equiv.species (ν_parallel₁ M), this ⟩,
    },
  end

private noncomputable def on_ν_drop₁ :
  ∀ {Γ ℓ k} {M : affinity ℍ}
    {A : species ℍ ω Γ} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , (ν(M) species.rename name.extend A) [ℓ, α]⟶ E
  → Σ' (E' : production ℍ ω Γ k) (eq : E ≈ E'), A [ℓ, α]⟶ E'
| Γ ℓ k M A α E t := begin
  generalize eqA : species.rename (@name.extend _ M.arity) A = A', rw eqA at t,

  cases t,
  case com₂ : a b B k' t' {
    subst eqA,

    rcases transition.rename_from name.extend t' with ⟨ ℓ₂, α₂, ⟨ E₂ ⟩ , t₂, eqℓ, eqα, eqE ⟩,
    cases α₂; unfold label.rename at eqα; try { contradiction },
    from false.elim (no_rename_zero (label.of_affinity.inj eqα))
  },
  case ν₁ : E t' {
    subst eqA,

    rcases transition.rename_from name.extend t' with ⟨ ℓ₂, α₂, E₂ , t₂, eqℓ, eqα, ⟨ eqE ⟩ ⟩,
    cases label.rename.inj (@name.extend.inj _ _) eqα,
    have : ℓ₂ = ℓ := lookup.rename.inj (@name.extend.inj _ _) eqℓ, subst this,

    cases E₂,
    case production.species { from ⟨ _, production.equiv.species (ν_drop₁ M), t₂ ⟩ },
    case production.concretion {
      from ⟨ _, production.equiv.concretion (concretion.equiv.ν_drop M), t₂ ⟩
    }
  }
end

private def on_ν_drop₂ :
  ∀ {Γ ℓ} {k} {M : affinity ℍ}
    {A : species ℍ ω Γ} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , A [ℓ, α]⟶ E
  → Σ' (E' : production ℍ ω Γ k) (eq : E ≈ E'), (ν(M) species.rename name.extend A) [ℓ, α]⟶ E'
  | Γ ℓ k M A α E t := begin
    have t' := ν₁ M (transition.rename name.extend t),
    cases E,
    case production.species {
      from ⟨ _, production.equiv.species (ν_drop₂ M), t' ⟩,
    },
    case production.concretion {
      from ⟨ _, production.equiv.concretion (symm (concretion.equiv.ν_drop M)), t' ⟩,
    }
  end

private def on_ν_swap₁ :
  ∀ {Γ ℓ k} {M N : affinity ℍ}
    {A : species ℍ ω (context.extend (N.arity) (context.extend (M.arity) Γ))}
    {α : label ℍ Γ k}
    {E : production ℍ ω Γ k}
    , (ν(M) ν(N) A) [ℓ, α]⟶ E
    → Σ' (E' : production ℍ ω Γ k) (eq : E ≈ E')
      , (ν(N) ν(M) species.rename name.swap A) [ℓ, α]⟶ E'
| Γ ℓ k M N A α E₁ t₁ := begin
  cases t₁,

  case ν₁ : E₂ t₂ {
    generalize eqα : label.rename (@name.extend _ M.arity) α = α₂, rw eqα at t₂,

    cases t₂,

    case ν₁ : E₃ t₃ {
      cases eqα,
      have t' := transition.rename name.swap t₃,

      rw [label.rename_compose, label.rename_compose, name.swap_comp_extend, name.ext_extend, ← label.rename_compose] at t',
      rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at t',

      refine ⟨ _, _, ν₁ N (ν₁ M t') ⟩,
      cases E₃,
      case production.species { from production.equiv.species (ν_swap₁ M N) },
      case production.concretion {
        from production.equiv.concretion (concretion.equiv.ν_swap M N),
      },
    },

    case com₂ : a b B k t₃ {
      cases α; unfold label.rename at eqα; try { contradiction }, cases eqα,

      have t' := transition.rename name.swap t₃,
      unfold label.rename at t', rw upair.map_beta name.swap _ _ at t', unfold name.swap at t',

      have t' :
        (species.rename name.swap A)
        [lookup.rename name.extend (lookup.rename name.extend ℓ),
         label.rename name.extend τ⟨ (upair.mk (name.zero a) (name.zero b)) ⟩]⟶
        (production.rename name.swap B),

        unfold label.rename, rw upair.map_beta name.extend _ _,
        rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at t',
        from t',

      have this := ν₁ M t',
      refine ⟨ _, production.equiv.species (ν_swap₁ M N), com₂ N _ this ⟩,
    }
  },

  case com₂ : a b B k t₂ {
    generalize eqB : production.species B = E, unfold_coes at t₂, rw eqB at t₂,
    cases t₂, cases t₂_E, cases eqB,

    have t' := transition.rename name.swap t₂_a,
    have :
      (ν(M) species.rename name.swap A)
      [_, label.rename name.extend τ@'(option.get k)]⟶
      ν(M) species.rename name.swap t₂_E_1,
      rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at t',
      from com₂ M _ t',
    have this := ν₁ N this,
    from ⟨ _, production.equiv.species (ν_swap₁ M N), this ⟩,
  }
end

private def on_ν_swap₂ :
  ∀ {Γ ℓ k} {M N : affinity ℍ}
    {A : species ℍ ω (context.extend (N.arity) (context.extend (M.arity) Γ))}
    {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , (ν(N) ν(M) species.rename name.swap A) [ℓ, α]⟶ E
  → Σ' (E' : production ℍ ω Γ k) (eq : E ≈ E'), (ν(M) ν(N) A) [ℓ, α]⟶ E'
| Γ ℓ k M N A α E t₁ := begin
  generalize eqA : species.rename name.swap A = A', rw eqA at t₁,
  cases t₁,

  case com₂ : a b B k t₂ {
    generalize eqB : production.species B = E, unfold_coes at t₂, rw eqB at t₂,
    cases t₂, subst eqA, cases t₂_E, cases eqB,

    have t' := transition.rename name.swap t₂_a,
    rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at t',

    have this := com₂ N k t',
    have : (ν(N) A ) [_, label.rename name.extend τ@'(option.get k)]⟶ ↑ν(N) species.rename name.swap t₂_E_1,
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
      subst eqA, subst eqα,

      have t' := transition.rename name.swap t₃,
      have : A [_, label.rename name.extend (label.rename name.extend α)]⟶ _,
        rw [species.rename_compose, name.swap_swap, species.rename_id] at t',
        rw [label.rename_compose, label.rename_compose, name.swap_comp_extend, name.ext_extend, ← label.rename_compose ] at t',
        rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at t',
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
      subst eqA,

      have t' :
        A
        [_, label.rename name.extend τ⟨ (upair.mk (name.zero a) (name.zero b)) ⟩]⟶
        (production.rename name.swap ↑B),
        have this := transition.rename name.swap t₃,

        unfold label.rename at this ⊢, rw upair.map_beta at this, rw upair.map_beta,
        rw [species.rename_compose, name.swap_swap, species.rename_id] at this,
        rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at this,

        from this,

      have this := ν₁ N t',
      from ⟨ _, production.equiv.species (ν_swap₁ N M), com₂ M k this ⟩,
    },
  }
end

/-- Convert a transition from one species to a transition from another
    equivalent species, with the same label and equivalent production. -/
noncomputable def equivalent_of :
  ∀ {Γ ℓ k} {A : species ℍ ω Γ} {B : species ℍ ω Γ} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , species.equivalent A B → A [ℓ, α]⟶ E
  → Σ' (E' : production ℍ ω Γ k) (eq : E ≈ E'), B [ℓ, α]⟶ E'
| Γ₁ ℓ₁ k₁ A₁ B₁ α₁ E₁ equ t₁ := begin
  induction equ generalizing k₁,

  case species.equivalent.refl { from ⟨ E₁, refl _, t₁ ⟩ },
  case species.equivalent.trans : Γ A B C ab bc ih_ab ih_bc {
    rcases ih_ab _ _ α₁ E₁ t₁ with ⟨ E₂, eq₂, t₂ ⟩,
    rcases ih_bc _ _ α₁ E₂ t₂ with ⟨ E₃, eq₃, t₃ ⟩,
    from ⟨ E₃, trans eq₂ eq₃, t₃ ⟩
  },

  case species.equivalent.ξ_parallel₁ : Γ A A' B eq ih {
    cases t₁,
    case com₁ : x y a b F G tf tg {
      rcases ih _ _ (#a) F tf with ⟨ F', equ, tf' ⟩,
      cases F' with _ b y' F',
      have tf'' : A' [ℓ₁, #a]⟶ ↑(production.cast_c equ),
        rw (production.cast_c.eq equ) at tf', from tf',

      from ⟨ concretion.pseudo_apply (production.cast_c equ) G,
             production.equiv.species (concretion.pseudo_apply.equiv (production.cast_c.equiv equ) (refl G)),
             com₁ tf'' tg ⟩
    },
    case parL : E t {
      rcases ih _ _ α₁ E t with ⟨ E', equ, t' ⟩,
      have eqE
        : (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E)
        ≈ (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E')
        := production.equiv.map
          (λ _ _, ξ_parallel₁) (λ _ _ _ _, concretion.equiv.ξ_parallel₁) equ,

      from ⟨ _, eqE, parL B t' ⟩
    },
    case parR : E t {
      have eqE
        : (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E)
        ≈ (production.map (λ x, A' |ₛ x) (λ _ _ x, A' |₂ x) E)
        := production.equiv.map_over
            (λ _, ξ_parallel₁ ⟨ eq ⟩) (λ _ _ _, concretion.equiv.ξ_parallel' ⟨ eq ⟩) E,
      from ⟨ _, eqE, parR A' t ⟩,
    }
  },

  case species.equivalent.ξ_parallel₂ : Γ A B B' eq ih {
    cases t₁,
    case com₁ : x y a b F G tf tg {
      rcases ih _ _ (#b) G tg with ⟨ G', equ, tg' ⟩,
      cases G' with _ b' y' G',
      have tg'' : B' [ℓ₁, #b]⟶ (production.cast_c equ),
        rw (production.cast_c.eq equ) at tg', from tg',

      from ⟨ concretion.pseudo_apply F (production.cast_c equ),
             production.equiv.species (concretion.pseudo_apply.equiv (refl F) (production.cast_c.equiv equ)),
             com₁ tf tg'' ⟩,
    },
    case parL : E t {
      have eqE
        : (production.map (λ x, x |ₛ B) (λ _ _ x, x |₁ B) E)
        ≈ (production.map (λ x, x |ₛ B') (λ _ _ x, x |₁ B') E)
        := production.equiv.map_over
            (λ _, ξ_parallel₂ ⟨ eq ⟩) (λ _ _ _, concretion.equiv.ξ_parallel ⟨ eq ⟩) E,
      from ⟨ _, eqE, parL B' t ⟩,
    },
    case parR : E t {
      rcases ih _ _ α₁ E t with ⟨ E', equ, t' ⟩,
      have eqE
        : (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E)
        ≈ (production.map (λ x, A |ₛ x) (λ _ _ x, A |₂ x) E')
        := production.equiv.map
          (λ _ _, ξ_parallel₂) (λ _ _ _ _, concretion.equiv.ξ_parallel₂) equ,
      from ⟨ _, eqE, parR A t' ⟩,
    }
  },

  case species.equivalent.ξ_restriction : Γ M A A' eq ih {
    cases t₁,

    case com₂ : a b B defn t {
      rcases ih _ _ τ⟨ name.zero a, name.zero b ⟩ B t with ⟨ E', equ, t' ⟩,
      cases E' with B',

      from ⟨ _, production.equiv.species (ξ_restriction M (production.equiv.unwrap_s equ)), com₂ M defn t' ⟩,
    },

    case ν₁ : E t {
      rcases ih _ _ (label.rename name.extend α₁) E t with ⟨ E', equ, t' ⟩,
      have eqE
        : (production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E)
        ≈ (production.map (λ x, ν(M) x) (λ _ _ x, ν'(M) x) E'),
        from production.equiv.map
          (λ _ _, ξ_restriction M) (λ _ _ _ _, concretion.equiv.ξ_restriction M) equ,

      from ⟨ _, eqE, ν₁ M t' ⟩,
    }
  },

  case species.equivalent.ξ_choice_here : Γ f π A A' As eq ih {
    cases t₁,
    case ξ_choice : t { refine ⟨ _, refl _, ξ_choice t ⟩ },
    case choice₁ : a b y {
      from ⟨ _, production.equiv.concretion (concretion.equiv.ξ_apply ⟨ eq ⟩), choice₁ a b y A' As ⟩,
    },
    case choice₂ : k { from ⟨ _, production.equiv.species ⟨ eq ⟩, choice₂ k A' As ⟩ },
  },

  case species.equivalent.ξ_choice_there : Γ f π A As As' eq ih {
    cases t₁,

    case ξ_choice : t {
      rcases ih _ _ α₁ E₁ t with ⟨ E', equ, t' ⟩,
      refine ⟨ _, equ, ξ_choice t' ⟩,
    },
    case choice₁ : a b y A As { from ⟨ _, refl _, choice₁ a b y A As' ⟩ },
    case choice₂ : k A As { from ⟨ _, refl _, choice₂ k A As' ⟩ },
  },

  case species.equivalent.parallel_nil₁ : Γ A {
    cases t₁,

    -- No such transition for (nil ⟶ _)
    case com₁ : x y a b F G tf tg { cases tg },
    case parR : E t { cases t },
    case parL : E t { from ⟨ _, production.equiv.parallel_nil E, t ⟩ },
  },

  case species.equivalent.parallel_nil₂ : Γ B {
    from ⟨ _, symm (production.equiv.parallel_nil E₁), parL species.nil t₁ ⟩
  },

  case species.equivalent.choice_swap { from on_choice_swap t₁ },

  case species.equivalent.parallel_assoc₁ { from on_parallel_assoc₁ t₁ },
  case species.equivalent.parallel_assoc₂ { from on_parallel_assoc₂ t₁ },

  case species.equivalent.parallel_symm { from on_parallel_symm t₁ },

  case species.equivalent.ν_parallel₁ { from on_ν_parallel₁ t₁ },
  case species.equivalent.ν_parallel₂ { from on_ν_parallel₂ t₁ },
  case species.equivalent.ν_drop₁ { from on_ν_drop₁ t₁ },
  case species.equivalent.ν_drop₂ { from on_ν_drop₂ t₁ },
  case species.equivalent.ν_swap₁ { from on_ν_swap₁ t₁ },
  case species.equivalent.ν_swap₂ { from on_ν_swap₂ t₁ },
end

/-- Wraps 'equivalent_of' into a 'transition_from' -/
noncomputable def equivalent_of.transition_from :
  ∀ {Γ ℓ} {A : species ℍ ω Γ} {B : species ℍ ω Γ}
  , species.equivalent A B
  → transition_from ℓ A → transition_from ℓ B
| Γ ℓ A B eq ⟨ k, α, E, t ⟩ :=
  let ⟨ E', _, t' ⟩ := equivalent_of eq t in
  ⟨ k, α, E', t' ⟩

/-- Show that 'equivalent_of' twice yields the same thing. This is not going to
    be fun. -/
axiom equivalent_of.transition_from_eq :
  ∀ {Γ ℓ} {A : species ℍ ω Γ} {B : species ℍ ω Γ}
    (eq : species.equivalent A B) (t : transition_from ℓ A)
  , t = equivalent_of.transition_from (species.equivalent.symm eq) (equivalent_of.transition_from eq t)

-/
/-- Show that two equivalent species's transition sets are equivalent. -/
noncomputable constant equivalent_of.is_equiv :
  ∀ {Γ ℓ} {A : species ℍ ω Γ} {B : species ℍ ω Γ}
  , species.equivalent A B
  → transition_from ℓ A ≃ transition_from ℓ B
/-
| Γ ℓ A B eq :=
{ to_fun := equivalent_of.transition_from eq,
  inv_fun := equivalent_of.transition_from (species.equivalent.symm eq),
  left_inv := λ x, symm (equivalent_of.transition_from_eq eq x),
  right_inv := λ x, begin
    have h := equivalent_of.transition_from_eq (species.equivalent.symm eq) x,
    rw ← species.equivalent.symm_symm eq at h,
    from symm h,
  end }
-/
end transition
end cpi

#lint-

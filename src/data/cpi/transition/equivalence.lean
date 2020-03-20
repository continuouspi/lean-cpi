import data.cpi.transition.basic

namespace cpi
namespace transition

variables {ℍ : Type} {ω : context}
open_locale congruence

open species.equiv

private def no_rename_zero {Γ} {n} {p : upair (fin n)} {q : upair (name Γ)}
  : upair.map name.extend q ≠ upair.map name.zero p
  := upair.rec_on q

    (λ a b eql, begin
      rcases upair.exists_rep p with ⟨ a', b', ⟨ _ ⟩ ⟩,
      rcases quotient.exact eql with ⟨ l, _ ⟩ | ⟨ l, _ ⟩; cases l
    end)
    (λ a b, function.hfunext (by rw upair.mk.comm) (λ a₂ b₂ _, heq.rfl))

private def on_parallel_assoc₁_left {Γ ℓ} {A B C : species ℍ ω Γ} :
  ∀ {α : label ℍ Γ kind.species} {E : species ℍ ω Γ}
  , (A |ₛ B) [ℓ, α]⟶ (production.species E)
  → Σ' E' (eq : production.species (E |ₛ C) ≈ E')
    , (A |ₛ B |ₛ C) [ℓ, α]⟶ E'
| α E (@com₁ _ _ _ _ x y _ _ a b F G _ _ rfl rfl tf tg) :=
  ⟨ _, production.equiv.species (symm (concretion.pseudo_apply.on_parallel₁ _ _ C)),
   com₁ rfl rfl tf (parL_concretion C tg) ⟩
| α E (parL_species C t) :=
  ⟨ _, production.equiv.species parallel_assoc₁, parL_species _ t ⟩
| α E (parR_species _ t) :=
  ⟨ _, production.equiv.species equiv.parallel_assoc₁, parR_species _ (parL_species _ t) ⟩

private def on_parallel_assoc₁ {Γ ℓ} {A B C : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , ((A |ₛ B) |ₛ C) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E'), (A |ₛ B |ₛ C) [ℓ, α]⟶ E'
| k α E (@com₁ _ _ _ _ x y _ _ a b _ G _ _ rfl rfl (parL_concretion D tf) tg) :=
  ⟨ _, production.equiv.species (concretion.pseudo_apply.parallel_shift _ B G),
   com₁ rfl rfl tf (parR_concretion _ tg) ⟩
| k α E (@com₁ _ _ _ _ x y _ _ a b _ G _ _ rfl rfl (parR_concretion D tf) tg) :=
  ⟨ _, production.equiv.species (concretion.pseudo_apply.on_parallel₂' A _ G),
   parR_species A (com₁ rfl rfl tf tg) ⟩
| k α E (parL_species _ t) := on_parallel_assoc₁_left t
| k α E (parL_concretion B (parL_concretion C t)) :=
  ⟨ _, production.equiv.concretion concretion.equiv.parallel_assoc₁, parL_concretion _ t ⟩
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
| ._ ._ ._ (@com₁ _ _ _ _ x y _ _ a b F G _ _ rfl rfl tf tg) := begin
    rw upair.eq a b,
    from ⟨ _, production.equiv.species (concretion.pseudo_apply.symm F G), com₁ rfl rfl tg tf ⟩
  end
| k α ._ (parL_species _ t) := ⟨ _, production.equiv.species parallel_symm, parR_species B t ⟩
| k α ._ (parL_concretion _ t) := ⟨ _, production.equiv.concretion concretion.equiv.parallel_symm, parR_concretion B t ⟩
| k α ._ (parR_species _ t) := ⟨ _, production.equiv.species parallel_symm, parL_species A t ⟩
| k α ._ (parR_concretion _ t) := ⟨ _, production.equiv.concretion (symm concretion.equiv.parallel_symm), parL_concretion A t ⟩

private def on_parallel_assoc₂_species {Γ ℓ} {A B C : species ℍ ω Γ} :
  ∀ {α : label ℍ Γ kind.species} {E : species ℍ ω Γ}
  , (B |ₛ C) [ℓ, α]⟶ (production.species E)
  → Σ' (E' : production ℍ ω Γ kind.species) (eq : production.species (A |ₛ E) ≈ E')
    , ((A |ₛ B) |ₛ C) [ℓ, α]⟶ E'
| α E (parL_species _ t) :=
  ⟨ _, production.equiv.species equiv.parallel_assoc₂, parL_species _ (parR_species _ t) ⟩
| α E (parR_species _ t) :=
  ⟨ _, production.equiv.species equiv.parallel_assoc₂, parR_species _ t ⟩
| α E (com₁ rfl rfl tf tg) :=
  ⟨ _, production.equiv.species (concretion.pseudo_apply.on_parallel₂' A _ _).symm,
   com₁ rfl rfl (parR_concretion _ tf) tg ⟩

private def on_parallel_assoc₂_concretion {Γ ℓ} {A B C : species ℍ ω Γ} {b y} :
  ∀ {α : label ℍ Γ kind.concretion} {E : concretion ℍ ω Γ b y}
  , (B |ₛ C) [ℓ, α]⟶ (production.concretion E)
  → Σ' (E' : production ℍ ω Γ kind.concretion) (eq : production.concretion (A |₂ E) ≈ E')
    , ((A |ₛ B) |ₛ C) [ℓ, α]⟶ E'
| α E (parL_concretion _ t) :=
  ⟨ _, production.equiv.concretion concretion.equiv.parallel_assoc₂.symm
   , parL_concretion _ (parR_concretion _ t) ⟩
| α E (parR_concretion _ t) :=
  ⟨ _, production.equiv.concretion concretion.equiv.parallel_assoc₃.symm, parR_concretion _ t ⟩

private def on_parallel_assoc₂ {Γ ℓ} {A B C : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , (A |ₛ B |ₛ C) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E'), ((A |ₛ B) |ₛ C) [ℓ, α]⟶ E'
| ._ α E (@com₁ _ _ _ _ x y _ _ a b F G _ _ rfl rfl tf (parL_concretion _ tg)) :=
  ⟨ _, production.equiv.species (concretion.pseudo_apply.on_parallel₁ F _ C),
   parL_species _ (com₁ rfl rfl tf tg) ⟩
| ._ α E (@com₁ _ _ _ _ x y _ _ a b F G _ _ rfl rfl tf (parR_concretion _ tg)) :=
  ⟨ _, production.equiv.species (concretion.pseudo_apply.parallel_shift F B _).symm,
    com₁ rfl rfl (parL_concretion _ tf) tg ⟩
| k α ._ (parL_species _ t) :=
  ⟨ _, production.equiv.species equiv.parallel_assoc₂, parL_species _ (parL_species _ t) ⟩
| k α ._ (parL_concretion _ t) :=
  ⟨ _, production.equiv.concretion concretion.equiv.parallel_assoc₁.symm, parL_concretion _ (parL_concretion _ t) ⟩
| k α ._ (parR_species _ t) := on_parallel_assoc₂_species t
| k α ._ (parR_concretion _ t) := on_parallel_assoc₂_concretion t

private def on_choice_swap {Γ ℓ} {As : choices ℍ ω Γ} :
  ∀ {k f g} {α : label ℍ Γ k}
    {π₁ : prefix_expr ℍ Γ f} {π₂ : prefix_expr ℍ Γ g}
    {A : species ℍ ω (f.apply Γ)} {B : species ℍ ω (g.apply Γ)}
    {E : production ℍ ω Γ k}
  , (Σ# whole.cons π₁ A (whole.cons π₂ B As)) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E')
    , (Σ# whole.cons π₂ B (whole.cons π₁ A As)) [ℓ, α]⟶ E'
| ._ α f g π₁ π₂ A B E (choice₁ a b b_len y _ _) := ⟨ _, refl _, ξ_choice (choice₁ a b b_len y _ _) ⟩
| ._ α f g π₁ π₂ A B E (choice₂ k _ _) := ⟨ _, refl _, ξ_choice (choice₂ k _ _) ⟩
| ._ α f g π₁ π₂ A B E (ξ_choice (choice₁ a b b_len y _ _)) := ⟨ _, refl _, choice₁ a b b_len y _ _ ⟩
| ._ α f g π₁ π₂ A B E (ξ_choice (choice₂ k _ _)) := ⟨ _, refl _, choice₂ k _ _ ⟩
| k α f g π₁ π₂ A B E (ξ_choice (ξ_choice t)) := ⟨ _, refl _, ξ_choice (ξ_choice t) ⟩

private def on_ν_parallel₂ {Γ ℓ} {M : affinity ℍ} {A : species ℍ ω Γ} {B : species ℍ ω (context.extend (M.arity) Γ)} :
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , (A |ₛ ν(M) B) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E'), (ν(M) rename name.extend A |ₛ B) [ℓ, α]⟶ E'
| ._ ._ _ (com₁ rfl rfl tf (ν₁_concretion M rfl tg)) :=
  -- Slighty bizzare, but the separate binding helps this to TC
  let tf' := transition.rename (@name.extend _ M.arity) tf in
  ⟨ _, production.equiv.species (concretion.pseudo_apply.on_restriction _ _ _),
    ν₁_species M rfl (com₁ rfl rfl tf' tg) ⟩
| k α _ (parL_species E t) :=
  let t' := transition.rename (@name.extend _ M.arity) t in
  ⟨ _, production.equiv.species (ν_parallel₂ M), ν₁_species M rfl (parL_species _ t' ) ⟩
| k α _ (parL_concretion E t) :=
  let t' := transition.rename (@name.extend _ M.arity) t in
  ⟨ _, production.equiv.concretion (concretion.equiv.ν_parallel₂ M).symm,
   ν₁_concretion M rfl (parL_concretion _ t' ) ⟩

| k α _ (parR_species A (com₂ M k' ek rfl t)) :=
  ⟨ _, production.equiv.species (ν_parallel₂ M), com₂ M k' ek rfl (parR_species _ t) ⟩
| k α _ (parR_species A (ν₁_species _ rfl t)) :=
  ⟨ _, production.equiv.species (ν_parallel₂ M), ν₁_species M rfl (parR_species _ t) ⟩
| k α _ (parR_concretion A (ν₁_concretion _ rfl t)) :=
  ⟨ _, production.equiv.concretion (concretion.equiv.ν_parallel₁ M).symm,
    ν₁_concretion M rfl (parR_concretion _ t) ⟩

private def upair_extend {n} {Γ} :
  ∀ {p : upair (name Γ)} {a b : name (context.extend n Γ)}
  , upair.map name.extend p = upair.mk a b
  → Σ' (a' b' : name Γ), p = upair.mk a' b' ∧ a = name.extend a' ∧ b = name.extend b'
| p (name.zero _) (name.zero _) e := false.elim (begin
  rcases quot.exists_rep p with ⟨ ⟨ a, b ⟩, ep ⟩, have : upair.mk a b = p := ep, subst this,
  rcases quotient.exact e with ⟨ l, r ⟩ | ⟨ l, r ⟩; contradiction,
end)
| p (name.zero _) (name.extend _) e := false.elim (begin
  rcases quot.exists_rep p with ⟨ ⟨ a, b ⟩, ep ⟩, have : upair.mk a b = p := ep, subst this,
  rcases quotient.exact e with ⟨ l, r ⟩ | ⟨ l, r ⟩; contradiction,
end)
| p (name.extend _) (name.zero _) e := false.elim (begin
  rcases quot.exists_rep p with ⟨ ⟨ a, b ⟩, ep ⟩, have : upair.mk a b = p := ep, subst this,
  rcases quotient.exact e with ⟨ l, r ⟩ | ⟨ l, r ⟩; contradiction,
end)
| p (name.extend a) (name.extend b) e := ⟨ a, b, begin
  have : upair.map name.extend p = upair.map name.extend (upair.mk a b) := e,
  from ⟨ upair.map.inj (@name.extend.inj _ _) this, rfl, rfl ⟩,
end ⟩

private noncomputable def on_ν_parallel₁_species {Γ ℓ} {M : affinity ℍ} {A : species ℍ ω Γ}
  {B : species ℍ ω (context.extend M.arity Γ)} :
  ∀ {A' : species ℍ ω (context.extend (M.arity) Γ)}
    {α' : label ℍ (context.extend M.arity Γ) kind.species}
    {α : label ℍ Γ kind.species}
    {E : species ℍ ω (context.extend M.arity Γ)}
  , (A' |ₛ B) [lookup.rename name.extend ℓ, α']⟶ (production.species E)
  → A' = rename name.extend A → α' = label.rename name.extend α
  → Σ' E' (eq : production.species (ν(M)E) ≈ E')
    , (A |ₛ ν(M) B) [ℓ, α]⟶ E'
| A' α' α E (parL_species _ t) eqA eqα := begin
  subst eqA, subst eqα,
  rcases transition.rename_from name.extend t with ⟨ α₂, ⟨ B ⟩, t₂, eα, eB ⟩,
  cases label.rename.inj (@name.extend.inj _ _) eα,
  rw ← production.species.inj eB,
  from ⟨ _, production.equiv.species (ν_parallel₁ M), parL_species _ t₂ ⟩,
end
| A' α' α E (parR_species _ t) eqA eqα := begin
  subst eqA, subst eqα,
  from ⟨ _, production.equiv.species (ν_parallel₁ M), parR_species _ (ν₁_species M rfl t) ⟩,
end
| A' α' α E (@com₁ _ _ _ _ x y _ _ a b F G _ _ rfl eα tf tg) eqA eqα := begin
  subst eqA, subst eqα,

  cases α with _ _ _ _ _ p,
  case label.spontanious { cases eα },

  rcases upair_extend (label.of_affinity.inj eα) with ⟨ a, b, ⟨ _ ⟩, ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
  rcases transition.rename_from name.extend tf with ⟨ ⟨ a₂ ⟩, ⟨ F ⟩, tf₂, ⟨ _ ⟩, ⟨ _ ⟩ ⟩,

  from ⟨ _, production.equiv.species (concretion.pseudo_apply.on_restriction _ M _).symm,
    com₁ rfl rfl tf₂ (ν₁_concretion M rfl tg) ⟩,
end

private noncomputable def on_ν_parallel₁_concretion {Γ ℓ} {M : affinity ℍ} {A : species ℍ ω Γ}
  {B : species ℍ ω (context.extend M.arity Γ)} {b y} :
  ∀ {A' : species ℍ ω (context.extend (M.arity) Γ)}
    {α' : label ℍ (context.extend M.arity Γ) kind.concretion}
    {α : label ℍ Γ kind.concretion}
    {E : concretion ℍ ω (context.extend M.arity Γ) b y}
  , (A' |ₛ B) [lookup.rename name.extend ℓ, α']⟶ (production.concretion E)
  → A' = rename name.extend A → α' = label.rename name.extend α
  → Σ' E' (eq : production.concretion (ν'(M)E) ≈ E')
    , (A |ₛ ν(M) B) [ℓ, α]⟶ E'
| A' α' α E (parL_concretion _ t) eqA eqα := begin
  subst eqA, subst eqα,
  rcases transition.rename_from name.extend t with ⟨ α₂, ⟨ B ⟩, t₂, eα, ⟨ _ ⟩ ⟩,
  cases label.rename.inj (@name.extend.inj _ _) eα,
  from ⟨ _, production.equiv.concretion (concretion.equiv.ν_parallel₂ M), parL_concretion _ t₂ ⟩,
end
| A' α' α E (parR_concretion _ t) eqA eqα := begin
  subst eqA, subst eqα,
  from ⟨ _, production.equiv.concretion (concretion.equiv.ν_parallel₁ M), parR_concretion _ (ν₁_concretion M rfl t) ⟩,
end

private noncomputable def on_ν_parallel₁ {Γ ℓ} {M : affinity ℍ} {A : species ℍ ω Γ}
  {B : species ℍ ω (context.extend (M.arity) Γ)} :
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , (ν(M) rename name.extend A |ₛ B) [ℓ, α]⟶ E
  → Σ' E' (eq : E ≈ E'), (A |ₛ ν(M) B) [ℓ, α]⟶ E'
| k α ._ (ν₁_species M rfl t) := on_ν_parallel₁_species t rfl rfl
| k α ._ (ν₁_concretion M rfl t) := on_ν_parallel₁_concretion t rfl rfl
| ._ α ._ (@com₂ _ _ _ _ M p q _ _ k ek rfl t) := begin
  generalize eqA : species.rename (@name.extend _ M.arity) A = A', rw eqA at t,

  cases t,
  case parL_species : E t {
    subst eqA, exfalso,
    rcases transition.rename_from name.extend t with ⟨ α₂, ⟨ E ⟩, tf₂, eα, eE ⟩, -- Annoying!

    cases α₂; simp only [label.rename] at eα,
    case label.spontanious { cases eα },
    from absurd eα no_rename_zero,
  },
  case parR_species : E t {
    subst eqA,
    from ⟨ _, production.equiv.species (ν_parallel₁ M), parR_species _ (com₂ M k ek rfl t ) ⟩,
  },
  case com₁ : x y a b F G eF eα tf tg {
    subst eqA, exfalso,

    rcases transition.rename_from name.extend tf with ⟨ α₂, ⟨ E ⟩, tf₂, eα', eE ⟩, -- Annoying!
    cases α₂, simp only [label.rename] at eα', subst eα',

    rcases upair.exists_rep p with ⟨ p₁, p₂, h ⟩, subst h,
    rcases quotient.exact (label.of_affinity.inj eα) with ⟨ l, r ⟩ | ⟨ l, r ⟩; contradiction,
  }
end

private noncomputable def on_ν_drop₁ {Γ ℓ} {M : affinity ℍ} {A : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , (ν(M) species.rename name.extend A) [ℓ, α]⟶ E
  → Σ' (E' : production ℍ ω Γ k) (eq : E ≈ E'), A [ℓ, α]⟶ E'
| k α E t := begin
  generalize eqA : species.rename (@name.extend _ M.arity) A = A', rw eqA at t,

  cases t,
  case com₂ : a b B k eqk eqα t' {
    subst eqA, subst eqα, exfalso,

    rcases transition.rename_from name.extend t' with ⟨ α₂, ⟨ E₂ ⟩ , t₂, eqα, eqE ⟩,
    cases α₂; simp only [label.rename] at eqα,
    case label.spontanious { cases eqα },
    from absurd eqα no_rename_zero,
  },
  case ν₁_species : α₁ α₂ E eα t' {
    subst eqA, subst eα,
    rcases transition.rename_from name.extend t' with ⟨ α₂, ⟨ E₂ ⟩ , t₂, eqα, eqE ⟩,
    cases label.rename.inj (@name.extend.inj _ _) eqα,
    rw ← production.species.inj eqE,
    from ⟨ _, production.equiv.species (ν_drop₁ M), t₂ ⟩,
  },
  case ν₁_concretion : α₁ α₂ b y E eα t' {
    subst eqA, subst eα,
    rcases transition.rename_from name.extend t' with ⟨ α₂, ⟨ E₂ ⟩ , t₂, eqα, ⟨ _ ⟩ ⟩,
    cases label.rename.inj (@name.extend.inj _ _) eqα,
    from ⟨ _, production.equiv.concretion (concretion.equiv.ν_drop M), t₂ ⟩,
  }
end

private def on_ν_drop₂ {Γ ℓ} {M : affinity ℍ} {A : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , A [ℓ, α]⟶ E
  → Σ' (E' : production ℍ ω Γ k) (eq : E ≈ E'), (ν(M) species.rename name.extend A) [ℓ, α]⟶ E'
| k α (production.species E) t :=
  let t' := transition.rename (@name.extend _ M.arity) t in
  ⟨ _, production.equiv.species (ν_drop₂ M), ν₁_species M rfl t' ⟩
| k α (production.concretion E) t :=
  let t' := transition.rename (@name.extend _ M.arity) t in
  ⟨ _, production.equiv.concretion (concretion.equiv.ν_drop M).symm, ν₁_concretion M rfl t' ⟩

private def on_ν_swap₁ {Γ ℓ} {M N : affinity ℍ} {A : species ℍ ω (context.extend (N.arity) (context.extend (M.arity) Γ))} :
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
    , (ν(M) ν(N) A) [ℓ, α]⟶ E
    → Σ' (E' : production ℍ ω Γ k) (eq : E ≈ E')
      , (ν(N) ν(M) species.rename name.swap A) [ℓ, α]⟶ E'
| ._ α E₁ (ν₁_species _ eα₁ (ν₁_species _ eα₂ t)) := begin
  subst eα₁, subst eα₂,
  have t' := transition.rename name.swap t,
  rw [label.rename_compose, label.rename_compose, name.swap_comp_extend, name.ext_extend, ← label.rename_compose] at t',
  rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at t',
  from ⟨ _, production.equiv.species (ν_swap₁ M N), ν₁_species N rfl (ν₁_species M rfl t' ) ⟩,
end
| ._ α E₁ (ν₁_species _ eα (com₂ _ k ek rfl t)) := begin
  cases α; simp only [label.rename] at eα,
  case label.of_affinity { contradiction },
  subst eα,

  have t' := transition.rename name.swap t,
  rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at t',
  refine ⟨ _, production.equiv.species (ν_swap₁ M N), com₂ N k ek rfl (ν₁_species M _ t') ⟩,

  simp only [label.rename, upair.map_compose, function.comp, name.swap],
end
| ._ α E₁ (ν₁_concretion _ rfl (ν₁_concretion _ rfl t)) := begin
  have t' := transition.rename name.swap t,
  rw [label.rename_compose, label.rename_compose, name.swap_comp_extend, name.ext_extend, ← label.rename_compose] at t',
  rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at t',
  from ⟨ _, production.equiv.concretion (concretion.equiv.ν_swap M N), ν₁_concretion N rfl (ν₁_concretion M rfl t' ) ⟩,
end
| ._ α E₁ (com₂ _ k ek rfl (ν₁_species _ rfl t)) := begin
  have t' := transition.rename name.swap t,
  rw [lookup.rename_compose, lookup.rename_compose, name.swap_comp_extend, name.ext_extend, ← lookup.rename_compose] at t',
  refine ⟨ _, production.equiv.species (ν_swap₁ M N), ν₁_species N rfl (com₂ M k ek _ t') ⟩,

  rw [upair.map_compose, upair.map_compose, name.swap_comp_extend, name.ext_zero],
end

private def on_ν_swap₂ {Γ ℓ} {M N : affinity ℍ} {A : species ℍ ω (context.extend (N.arity) (context.extend (M.arity) Γ))}:
  ∀ {k} {α : label ℍ Γ k} {E : production ℍ ω Γ k}
  , (ν(N) ν(M) species.rename name.swap A) [ℓ, α]⟶ E
  → Σ' (E' : production ℍ ω Γ k) (eq : E ≈ E'), (ν(M) ν(N) A) [ℓ, α]⟶ E'
| k α E₁ t := begin
  rcases on_ν_swap₁ t with ⟨ E', eqE, t' ⟩,
  rw [species.rename_compose, name.swap_swap, species.rename_id] at t',
  from ⟨ E', eqE, t' ⟩,
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
    case com₁ : x y a b F G E' α' eE eα tf tg {
      subst eE, subst eα,
      rcases ih _ _ (#a) _ tf with ⟨ F', equ, tf' ⟩, cases F' with _ b y' F',
      rcases production.equiv.arity equ with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,

      from ⟨ _, production.equiv.species (concretion.pseudo_apply.equiv (production.equiv.unwrap_c equ) (refl G)),
             com₁ rfl rfl tf' tg ⟩,
    },
    case parL_species : α' E t {
      rcases ih _ _ _ _ t with ⟨ E', equ, t' ⟩, cases E',
      from ⟨ _, production.equiv.species (ξ_parallel₁ (production.equiv.unwrap_s equ)), parL_species B t' ⟩
    },
    case parL_concretion : α' b y E t {
      rcases ih _ _ _ _ t with ⟨ E', equ, t' ⟩, cases E',
      rcases production.equiv.arity equ with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from ⟨ _, production.equiv.concretion (concretion.equiv.ξ_parallel₁ (production.equiv.unwrap_c equ)),
        parL_concretion _ t' ⟩,
    },
    case parR_species : α' E t {
      from ⟨ _, production.equiv.species (ξ_parallel₁ ⟨ eq ⟩), parR_species _ t ⟩,
    },
    case parR_concretion : α' b y E t {
      from ⟨ _, production.equiv.concretion (concretion.equiv.ξ_parallel' ⟨ eq ⟩), parR_concretion _ t ⟩,
    },
  },

  case species.equivalent.ξ_parallel₂ : Γ A B B' eq ih {
    cases t₁,
    case com₁ : x y a b F G E' α' eE eα tf tg {
      subst eE, subst eα,
      rcases ih _ _ (#b) _ tg with ⟨ G', equ, tg' ⟩, cases G' with _ b y' G',
      rcases production.equiv.arity equ with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from ⟨ _, production.equiv.species (concretion.pseudo_apply.equiv (refl F) (production.equiv.unwrap_c equ)),
             com₁ rfl rfl tf tg' ⟩,
    },
    case parL_species : α' E t {
      from ⟨ _, production.equiv.species (ξ_parallel₂ ⟨ eq ⟩), parL_species _ t ⟩,
    },
    case parL_concretion : α' b y E t {
      from ⟨ _, production.equiv.concretion (concretion.equiv.ξ_parallel ⟨ eq ⟩), parL_concretion _ t ⟩,
    },
    case parR_species : α' E t {
      rcases ih _ _ _ _ t with ⟨ E', equ, t' ⟩, cases E',
      from ⟨ _, production.equiv.species (ξ_parallel₂ (production.equiv.unwrap_s equ)), parR_species _ t' ⟩
    },
    case parR_concretion : α' b y E t {
      rcases ih _ _ _ _ t with ⟨ E', equ, t' ⟩, cases E',
      rcases production.equiv.arity equ with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from ⟨ _, production.equiv.concretion (concretion.equiv.ξ_parallel₂ (production.equiv.unwrap_c equ)),
        parR_concretion _ t' ⟩,
    },
  },

  case species.equivalent.ξ_restriction : Γ M A A' eq ih {
    cases t₁,

    case com₂ : p p' B k ek ep t {
      rcases ih _ _ _ _ t with ⟨ E', equ, t' ⟩,
      cases E' with B',

      from ⟨ _, production.equiv.species (ξ_restriction M (production.equiv.unwrap_s equ)), com₂ M k ek ep t' ⟩,
    },
    case ν₁_species : α α' E eα t {
      rcases ih _ _ _ _ t with ⟨ E', equ, t' ⟩, cases E',
      from ⟨ _, production.equiv.species (ξ_restriction M (production.equiv.unwrap_s equ)),
        ν₁_species M eα t' ⟩,
    },
    case ν₁_concretion : α α' b y E eα t {
      rcases ih _ _ _ _ t with ⟨ E', equ, t' ⟩, cases E',
      rcases production.equiv.arity equ with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from ⟨ _, production.equiv.concretion (concretion.equiv.ξ_restriction M (production.equiv.unwrap_c equ)),
        ν₁_concretion M eα t' ⟩,
    },
  },

  case species.equivalent.ξ_choice_here : Γ f π A A' As eq ih {
    cases t₁,
    case ξ_choice : t { refine ⟨ _, refl _, ξ_choice t ⟩ },
    case choice₁ : a n b b_len y {
      from ⟨ _, production.equiv.concretion (concretion.equiv.ξ_apply ⟨ eq ⟩), choice₁ a b b_len y A' As ⟩,
    },
    case choice₂ : k { from ⟨ _, production.equiv.species ⟨ eq ⟩, choice₂ k A' As ⟩ },
  },

  case species.equivalent.ξ_choice_there : Γ f π A As As' eq ih {
    cases t₁,

    case ξ_choice : t {
      rcases ih _ _ α₁ E₁ t with ⟨ E', equ, t' ⟩,
      refine ⟨ _, equ, ξ_choice t' ⟩,
    },
    case choice₁ : a n b b_len y A As { from ⟨ _, refl _, choice₁ a b b_len y A As' ⟩ },
    case choice₂ : k A As { from ⟨ _, refl _, choice₂ k A As' ⟩ },
  },

  case species.equivalent.parallel_nil₁ : Γ A {
    cases t₁,

    -- No such transition for (nil ⟶ _)
    case com₁ : x y a b F G FG α eFG eα tf tg { cases tg },
    case parR_species : α E t { cases t },
    case parR_concretion : α b y E t { cases t },
    case parL_species : α E t { from ⟨ _, production.equiv.species parallel_nil₁, t ⟩ },
    case parL_concretion : α b y E t { from ⟨ _, production.equiv.concretion concretion.equiv.parallel_nil, t ⟩ },
  },

  case species.equivalent.parallel_nil₂ : Γ B {
    cases E₁,
    case production.species { from ⟨ _, production.equiv.species parallel_nil₂, parL_species _ t₁ ⟩ },
    case production.concretion { from ⟨ _, production.equiv.concretion concretion.equiv.parallel_nil.symm, parL_concretion _ t₁ ⟩ },
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
noncomputable def equivalent_of.transition_from {Γ ℓ} {A B : species ℍ ω Γ} :
  species.equivalent A B → transition_from ℓ A → transition_from ℓ B
| eq ⟨ k, α, E, t ⟩ :=
  let ⟨ E', _, t' ⟩ := equivalent_of eq t in
  ⟨ k, α, E', t' ⟩

/-- Show that 'equivalent_of' twice yields the same thing. This is not going to
    be fun. -/
axiom equivalent_of.transition_from_eq :
  ∀ {Γ ℓ} {A : species ℍ ω Γ} {B : species ℍ ω Γ}
    (eq : species.equivalent A B) (t : transition_from ℓ A)
  , equivalent_of.transition_from (species.equivalent.symm eq) (equivalent_of.transition_from eq t) = t

/-- Show that two equivalent species's transition sets are equivalent. -/
noncomputable def equivalent_of.is_equiv {Γ ℓ} {A B : species ℍ ω Γ} (eq : species.equivalent A B)
  : transition_from ℓ A ≃ transition_from ℓ B
  := { to_fun := equivalent_of.transition_from eq,
       inv_fun := equivalent_of.transition_from (species.equivalent.symm eq),
       left_inv := equivalent_of.transition_from_eq eq,
       right_inv := λ x, begin
         have h := equivalent_of.transition_from_eq eq.symm x,
         rw ← species.equivalent.symm_symm eq at h,
         from h,
       end }

end transition
end cpi

#lint-

import data.cpi.transition.basic data.multiset2

namespace cpi
namespace transition

variables {ℍ : Type} {ω : context}

/-- The set of all transitions from a nil species. -/
def enumerate_nil {Γ} {ℓ : lookup ℍ ω Γ}
  : fintype (transition.transition_from ℓ species.nil)
  := ⟨ finset.empty, (λ ⟨ k, α, E, t ⟩, by cases t) ⟩

/-- ξ_choice acts as an embedding. This is effectively ξ_choice.inj but lifted
    to transitions. -/
def ξ_choice.embed
    {Γ f} (ℓ : lookup ℍ ω Γ)
    (π : prefix_expr ℍ Γ f) (A : species ℍ ω (f.apply Γ)) (As : species.choices ℍ ω Γ)
  : transition_from ℓ (Σ# As) ↪ transition_from ℓ (Σ# (whole.cons π A As))
  := { to_fun := λ t, transition_from.mk (ξ_choice t.2.2.2),
       inj := λ ⟨ k, α, E, t ⟩ ⟨ k', α', E', t' ⟩ eq, by { cases eq, from rfl} }

private def enumerate_choice_communicate_ts {Γ} (ℓ : lookup ℍ ω Γ) :
  ∀ (a :  name Γ) (b : list (name Γ)) (y : ℕ)
    (A : species ℍ ω (context.extend y Γ))
    {As : species.choices ℍ ω Γ}
  , fintype (transition_from ℓ (Σ# As))
  → finset (transition_from ℓ (Σ# (whole.cons (a#(b;y)) A As)))
| a b y A As child :=
  finset.insert_nmem'
    (transition_from.mk (choice₁ a b rfl y A As))
    (finset.map (ξ_choice.embed ℓ _ A As) child.elems)
    (λ mem, begin
      rcases finset.mem_map.mp mem with ⟨ ⟨ k, α, E, t ⟩, mem, eql ⟩,

      unfold_coes at eql,
      simp only [ξ_choice.embed, transition_from.mk] at eql,
      unfold_projs at eql,
      cases eql,
    end)

private def enumerate_choice_communicate {Γ} (ℓ : lookup ℍ ω Γ) :
  ∀ (a :  name Γ) (b : list (name Γ)) (y : ℕ)
    (A : species ℍ ω (context.extend y Γ))
    {As : species.choices ℍ ω Γ}
  , fintype (transition_from ℓ (Σ# As))
  → fintype (transition_from ℓ (Σ# (whole.cons (a#(b;y)) A As)))
| a b y A As child :=
  { elems := enumerate_choice_communicate_ts ℓ a b y A child,
    complete := λ x, begin
      rcases x with ⟨ k, α, E, t ⟩,
      cases t,
      case ξ_choice {
        have : transition_from.mk t_a ∈ child.elems := @fintype.complete _ child _,
        have this := finset.mem_map_of_mem (ξ_choice.embed ℓ (a#(b;y)) A As) this,
        from finset.mem_insert_nmem_of_mem this _,
      },
      case choice₁ {
        subst t_b_len,
        from finset.mem_insert_nmem_self _
      },
    end }

private def enumerate_choice_spontanious_ts {Γ} (ℓ : lookup ℍ ω Γ) :
  ∀ (k : ℍ) (A : species ℍ ω Γ) {As : species.choices ℍ ω Γ}
  , fintype (transition_from ℓ (Σ# As))
  → finset (transition_from ℓ (Σ# (whole.cons (τ@k) A As)))
| k A As child :=
  finset.insert_nmem'
    (transition_from.mk (choice₂ k A As))
    (finset.map (ξ_choice.embed ℓ _ A As) child.elems)
    (λ mem, begin
      rcases finset.mem_map.mp mem with ⟨ ⟨ k, α, E, t ⟩, mem, eql ⟩,

      unfold_coes at eql,
      simp only [ξ_choice.embed, transition_from.mk] at eql,
      unfold_projs at eql,
      cases eql,
    end)

private def enumerate_choice_spontanious {Γ} (ℓ : lookup ℍ ω Γ) :
  ∀ (k : ℍ) (A : species ℍ ω Γ) {As : species.choices ℍ ω Γ}
  , fintype (transition_from ℓ (Σ# As))
  → fintype (transition_from ℓ (Σ# (whole.cons (τ@k) A As)))
| k A As child :=
  { elems := enumerate_choice_spontanious_ts ℓ k A child,
    complete := λ x, begin
      rcases x with ⟨ k', α, E, t ⟩,
      cases t,
      case ξ_choice {
        have : transition_from.mk t_a ∈ child.elems := @fintype.complete _ child _,
        have this := finset.mem_map_of_mem (ξ_choice.embed ℓ (τ@k) A As) this,
        from finset.mem_insert_nmem_of_mem this _,
      },
      case choice₂ { from finset.mem_insert_nmem_self _ },
    end }

/-- The set of all transitions from a guarded choice species. -/
def enumerate_choices {Γ} (ℓ : lookup ℍ ω Γ) :
  ∀ (As : species.choices ℍ ω Γ), fintype (transition_from ℓ (Σ# As))
| species.whole.empty :=
  { elems := finset.empty,
    complete := λ ⟨ k, α, E, t ⟩, by cases t }
| (species.whole.cons (a#(b; y)) A As) := enumerate_choice_communicate ℓ a b y A (enumerate_choices As)
| (species.whole.cons (τ@k) A As) := enumerate_choice_spontanious ℓ k A (enumerate_choices As)

private def defn.from {Γ n} (ℓ : lookup ℍ ω Γ) (D : reference n ω) (as : vector (name Γ) n)
  : transition_from ℓ (Σ# (species.rename (name.mk_apply as) (ℓ _ D)))
  → transition_from ℓ (apply D as)
| ⟨ k, α, E, t ⟩ := ⟨ k, α, E, defn _ _ _ _ rfl t ⟩

private def defn.embed {Γ n} (ℓ : lookup ℍ ω Γ) (D : reference n ω) (as : vector (name Γ) n)
  : transition_from ℓ (Σ# (species.rename (name.mk_apply as) (ℓ _ D)))
  ↪ transition_from ℓ (apply D as)
  := ⟨ defn.from ℓ D as, λ t t' eql, begin
    rcases t with ⟨ k, α, E, t ⟩, rcases t' with ⟨ k', α', E', t' ⟩,
    simp only [defn.from] at eql,

    rcases psigma.mk.inj eql with ⟨ ⟨ _ ⟩, eql₁ ⟩, clear eql,
    rcases psigma.mk.inj (eq_of_heq eql₁) with ⟨ ⟨ _ ⟩, eql₂ ⟩, clear eql₁,
    rcases psigma.mk.inj (eq_of_heq eql₂) with ⟨ ⟨ _ ⟩, eql₃ ⟩, clear eql₂,
    have eql := eq_of_heq (defn.inj (eq_of_heq eql₃)).2, clear eql₃, subst eql,
  end ⟩

private def enumerate_apply_ts {Γ n} (ℓ : lookup ℍ ω Γ) (D : reference n ω) (as : vector (name Γ) n)
  : finset (transition_from ℓ (apply D as))
  := finset.map (defn.embed ℓ D as)
      (enumerate_choices ℓ (species.rename (name.mk_apply as) (ℓ _ D))).elems

private lemma enumerate_apply_complete {Γ n} (ℓ : lookup ℍ ω Γ) (D : reference n ω) (as : vector (name Γ) n)
  : ∀ x, x ∈ enumerate_apply_ts ℓ D as
| ⟨ k, α, E, defn ℓ' D as B eql t ⟩ := begin
  subst eql,
  have h :=
    @fintype.complete _
      (enumerate_choices ℓ (species.rename (name.mk_apply as) (ℓ _ D)))
      (transition_from.mk t),
  from finset.mem_map_of_mem (defn.embed ℓ D as) h,
end

/-- The set of all transitions from a species invocation. -/
def enumerate_apply {Γ n} (ℓ : lookup ℍ ω Γ) (D : reference n ω) (as : vector (name Γ) n)
  : fintype (transition_from ℓ (apply D as)) :=
  ⟨ enumerate_apply_ts ℓ D as, enumerate_apply_complete ℓ D as ⟩

/-- Wrap a transition in parL. -/
def parL {Γ : context} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : transition.transition_from ℓ A → transition.transition_from ℓ (A |ₛ B)
| ⟨ _, α, production.species E, t ⟩ := ⟨ _, α, _, transition.parL_species B t ⟩
| ⟨ _, α, production.concretion E, t ⟩ := ⟨ _, α, _, transition.parL_concretion B t ⟩

/-- Wrap a transition in parL, as a function embedding. -/
def parL.embed {Γ} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : transition.transition_from ℓ A ↪ transition.transition_from ℓ (A |ₛ B)
  := ⟨ parL A B, λ t t' eq, begin
        rcases t with ⟨ k, α, E, t ⟩, rcases t' with ⟨ k', α', E', t' ⟩,
          cases E; cases E'; cases eq; from rfl,
        end ⟩

/-- Wrap a transition in parR. -/
def parR {Γ} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : transition.transition_from ℓ B → transition.transition_from ℓ (A |ₛ B)
| ⟨ _, α, production.species E, t ⟩ := ⟨ _, α, _, transition.parR_species A t ⟩
| ⟨ _, α, production.concretion E, t ⟩ := ⟨ _, α, _, transition.parR_concretion A t ⟩

/-- Wrap a transition in parL, as a function embedding. -/
def parR.embed {Γ} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : transition.transition_from ℓ B ↪ transition.transition_from ℓ (A |ₛ B)
  := ⟨ parR A B, λ t t' eq, begin
        rcases t with ⟨ k, α, E, t ⟩, rcases t' with ⟨ k', α', E', t' ⟩,
          cases E; cases E'; cases eq; from rfl,
        end ⟩

/-- Determine if two transitions result have products with compatible
    concretions. -/
private def com₁.is_compatible {Γ} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : transition.transition_from ℓ A × transition.transition_from ℓ B
  → Prop
| ⟨ ⟨ _, l, @production.concretion _ _ _ a x F, t ⟩,
    ⟨ _, l', @production.concretion _ _ _ b y G, t' ⟩ ⟩ := a = y ∧ b = x
| ⟨ ⟨ _, l, production.concretion F, t ⟩, ⟨ _, l', production.species G, t' ⟩ ⟩ := false
| ⟨ ⟨ _, l, production.species F, t ⟩, ⟨ _, l', production.concretion G, t' ⟩ ⟩ := false
| ⟨ ⟨ _, l, production.species F, t ⟩, ⟨ _, l', production.species G, t' ⟩ ⟩ := false

instance com₁.is_compatible.decide {Γ} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : decidable_pred (com₁.is_compatible ℓ A B)
| ⟨ ⟨ _, l, @production.concretion _ _ _ a x F, t ⟩,
    ⟨ _, l', @production.concretion _ _ _ b y G, t' ⟩ ⟩
    := by { unfold com₁.is_compatible, by apply_instance }
| ⟨ ⟨ _, l, production.concretion F, t ⟩, ⟨ _, l', production.species G, t' ⟩ ⟩ := decidable.false
| ⟨ ⟨ _, l, production.species F, t ⟩, ⟨ _, l', production.concretion G, t' ⟩ ⟩ := decidable.false
| ⟨ ⟨ _, l, production.species F, t ⟩, ⟨ _, l', production.species G, t' ⟩ ⟩ := decidable.false

/-- The subtype of all transition pairs which are compatible. -/
@[nolint has_inhabited_instance]
def com₁.compatible {Γ} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) : Type
  := { p : transition.transition_from ℓ A × transition.transition_from ℓ B
     // com₁.is_compatible ℓ A B p }

/-- Convert a compatible pair of transitions to a com₁ transition. -/
def com₁.of_compatible {Γ} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : com₁.compatible ℓ A B → transition.transition_from ℓ (A |ₛ B)
| ⟨ ⟨ ⟨ _, l, @production.concretion _ _ _ a x F, t ⟩,
     ⟨ _, l', @production.concretion _ _ _ b y G, t' ⟩ ⟩, p ⟩ := begin
  cases l with _ a, cases l' with _ b, rcases p with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
  refine ⟨ _, _, _, com₁ rfl rfl t t' ⟩,
end
| ⟨ ⟨ ⟨ _, l, production.concretion F, t ⟩, ⟨ _, l', production.species G, t' ⟩ ⟩, p ⟩ := false.elim p
| ⟨ ⟨ ⟨ _, l, production.species F, t ⟩, ⟨ _, l', production.concretion G, t' ⟩ ⟩, p ⟩ := false.elim p
| ⟨ ⟨ ⟨ _, l, production.species F, t ⟩, ⟨ _, l', production.species G, t' ⟩ ⟩, p ⟩ := false.elim p

/-- We need a separate lemma to show com₁.of_compatible - we need to
    generalise several variables, otherwise the case splits do not go through.
-/
private lemma com₁.of_compatible.inj_help {Γ} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ) :
  ∀ {a x} {a₁ b₁} {F₁ : concretion ℍ ω Γ a x} {G₁ : concretion ℍ ω Γ x a}
    {b y} {a₂ b₂} {F₂ : concretion ℍ ω Γ b y} {G₂ : concretion ℍ ω Γ y b}
    {FG₁ FG₂ : species ℍ ω Γ} {α₁ α₂ : label ℍ Γ kind.species}
    (eFG₁ : FG₁ = concretion.pseudo_apply F₁ G₁)
    (eFG₂ : FG₂ = concretion.pseudo_apply F₂ G₂)
    (eα₁ : α₁ = τ⟨ a₁, b₁ ⟩) (eα₂ : α₂ = τ⟨ a₂, b₂ ⟩)
    (tf₁ : A [ℓ, #a₁]⟶ (production.concretion F₁)) (tg₁ : B [ℓ, #b₁]⟶ (production.concretion G₁))
    (tf₂ : A [ℓ, #a₂]⟶ (production.concretion F₂)) (tg₂ : B [ℓ, #b₂]⟶ (production.concretion G₂))
  , (τ⟨ a₁, b₁ ⟩ = (τ⟨ a₂, b₂ ⟩ : label ℍ Γ _))
  → psigma.mk (production.species FG₁) (com₁ eFG₁ eα₁ tf₁ tg₁)
  == psigma.mk (production.species FG₂) (com₁ eFG₂ eα₂ tf₂ tg₂)
  → a = b ∧ x = y ∧ a₁ = a₂ ∧ b₁ = b₂ ∧ F₁ == F₂ ∧ G₁ == G₂ ∧ tf₁ == tf₂ ∧ tg₁ == tg₂
| a x a₁ b₁ F₁ G₁ b y a₂ b₂ F₂ G₂ FG₁ FG₂ α₁ α₂ eFG₁ eFG₂ eα₁ eα₂
  tf₁ tg₁ tf₂ tg₂ eqα eqT := begin
  have : α₁ = α₂ := trans eα₁ (trans eqα eα₂.symm), subst this,
  rcases psigma.mk.inj (eq_of_heq eqT) with ⟨ eqFG, eqT ⟩,
  have : FG₁ = FG₂ := production.species.inj eqFG, subst this,

  rcases com₁.inj (eq_of_heq eqT) with ⟨ ⟨ _ ⟩, ⟨ _ ⟩, ⟨ _ ⟩, ⟨ _ ⟩, F, G, tf, tg ⟩,
  from ⟨ rfl, rfl, rfl, rfl, F, G, tf, tg ⟩,
end

private lemma com₁.of_compatible.inj {Γ} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : function.injective (com₁.of_compatible ℓ A B)
| ⟨ ⟨ ⟨ k₁, α₁, E₁, t₁ ⟩, ⟨ k₁', α₁', E₁', t₁' ⟩ ⟩, is₁ ⟩
  ⟨ ⟨ ⟨ k₂, α₂, E₂, t₂ ⟩, ⟨ k₂', α₂', E₂', t₂' ⟩ ⟩, is₂ ⟩ eql := begin
  cases E₁; cases E₁'; try { unfold com₁.is_compatible at is₁, contradiction },
  rcases is₁ with ⟨ l, r ⟩, subst l, subst r, cases α₁, cases α₁',

  cases E₂; cases E₂'; try { unfold com₁.is_compatible at is₂, contradiction },
  rcases is₂ with ⟨ l, r ⟩, subst l, subst r, cases α₂, cases α₂',

  simp only [com₁.of_compatible] at eql,

  rcases psigma.mk.inj (eq_of_heq (psigma.mk.inj eql).2) with ⟨ eqα, eqT ⟩,
  rcases com₁.of_compatible.inj_help A B rfl rfl rfl rfl t₁ t₁' t₂ t₂' eqα eqT
    with ⟨ ⟨ _ ⟩, ⟨ _ ⟩, ⟨ _ ⟩, ⟨ _ ⟩, ⟨ _ ⟩, ⟨ _ ⟩, ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
  from rfl,
end

/-- Convert a compatible pair of transitions to a com₁ transition. -/
def com₁.embed {Γ} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : com₁.compatible ℓ A B ↪ transition.transition_from ℓ (A |ₛ B)
  := ⟨ com₁.of_compatible ℓ A B, com₁.of_compatible.inj A B ⟩

private lemma com₁.impossible_l {Γ}
    (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) {b y}
    {F : concretion ℍ ω Γ b y} {G : concretion ℍ ω Γ y b}
  : ∀ {a₁ a₂} {C FG : species ℍ ω Γ}
      (t : A [ℓ, τ⟨ a₁, a₂ ⟩]⟶ (production.species C))
      (t₁ : A [ℓ, #a₁]⟶ (production.concretion F))
      (t₂ : B [ℓ, #a₂]⟶ (production.concretion G))
      (h : FG = concretion.pseudo_apply F G)
    , (C |ₛ B) = FG
    → ¬ (parL_species B t == com₁ h rfl t₁ t₂)
| a₁ a₂ C FG t t₁ t₂ h cfg eql := by { subst cfg, cases (eq_of_heq eql) }

private lemma com₁.impossible_r {Γ}
    (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) {b y}
    {F : concretion ℍ ω Γ b y} {G : concretion ℍ ω Γ y b}
  : ∀ {a₁ a₂} {C FG : species ℍ ω Γ}
      (t : B [ℓ, τ⟨ a₁, a₂ ⟩]⟶ (production.species C))
      (t₁ : A [ℓ, #a₁]⟶ (production.concretion F))
      (t₂ : B [ℓ, #a₂]⟶ (production.concretion G))
      (h : FG = concretion.pseudo_apply F G)
    , (A |ₛ C) = FG
    → ¬ (parR_species A t == com₁ h rfl t₁ t₂)
| a₁ a₂ C FG t t₁ t₂ h cfg eql := by { subst cfg, cases (eq_of_heq eql) }

private def enumerate_parallel_ts {Γ} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : fintype (transition.transition_from ℓ A)
  → fintype (transition.transition_from ℓ B)
  → finset (transition.transition_from ℓ (A |ₛ B))
| As Bs :=
  finset.union_disjoint
    (finset.map
      (com₁.embed ℓ A B)
      ((finset.product As.elems Bs.elems).subtype (com₁.is_compatible ℓ A B)))
    (finset.union_disjoint
      (As.elems.map (parL.embed A B))
      (Bs.elems.map (parR.embed A B))
      (λ x memL memR, begin
        rcases finset.mem_map.mp memL with ⟨ ⟨ k, α, E, t ⟩, mem, eql ⟩, clear mem,
        unfold_coes at eql, simp only [parL.embed] at eql, subst eql,

        rcases finset.mem_map.mp memR with ⟨ ⟨ k', α', E', t' ⟩, mem, eql ⟩, clear mem,
        unfold_coes at eql, simp only [parR.embed] at eql,

        cases E; cases E'; simp only [parL, parR] at eql; cases eql,
      end))
    (λ x memL memR, begin
      rcases finset.mem_map.mp memL with ⟨ ⟨ ⟨ ⟨ k₁, α₁, E₁, t₁ ⟩, ⟨ k₂, α₂, E₂, t₂ ⟩ ⟩, d ⟩, mem, eql ⟩, clear memL mem,
      unfold_coes at eql, simp only [com₁.embed] at eql,
      cases E₁; cases E₂; try { simpa only [com₁.is_compatible] using d },
      rcases d with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩, cases α₁, cases α₂,
      simp only [com₁.of_compatible] at eql, subst eql,

      cases finset.mem_union_disjoint.mp memR,
      case or.inl {
        rcases finset.mem_map.mp h with ⟨ ⟨ k, α, E, t ⟩, mem, eql ⟩, clear mem memR,
        unfold_coes at eql, simp only [parL.embed] at eql,
        cases E,
        case production.species {
          rcases psigma.mk.inj eql with ⟨ ⟨ _ ⟩, eql₁ ⟩, clear eql,
          rcases psigma.mk.inj (eq_of_heq eql₁) with ⟨ ⟨ _ ⟩, eql₂ ⟩, clear eql₁,
          rcases psigma.mk.inj (eq_of_heq eql₂) with ⟨ eqlE, eqlT ⟩,

          from com₁.impossible_l ℓ A B t t₁ t₂ rfl (production.species.inj eqlE) eqlT,
        },
        case production.concretion { cases (psigma.mk.inj eql).1 },
      },
      case or.inr {
        rcases finset.mem_map.mp h with ⟨ ⟨ k, α, E, t ⟩, mem, eql ⟩, clear mem memR,
        unfold_coes at eql, simp only [parR.embed] at eql,
        cases E,
        case production.species {
          rcases psigma.mk.inj eql with ⟨ ⟨ _ ⟩, eql₁ ⟩, clear eql,
          rcases psigma.mk.inj (eq_of_heq eql₁) with ⟨ ⟨ _ ⟩, eql₂ ⟩, clear eql₁,
          rcases psigma.mk.inj (eq_of_heq eql₂) with ⟨ eqlE, eqlT ⟩,

          from com₁.impossible_r ℓ A B t t₁ t₂ rfl (production.species.inj eqlE) eqlT,
        },
        case production.concretion { cases (psigma.mk.inj eql).1 },
      },
    end)

private lemma enumate_parallel_compute_l
    {Γ ℓ} {A B : species ℍ ω Γ} {l : label ℍ Γ kind.species} {E}
    (As : fintype (transition_from ℓ A)) (Bs : fintype (transition_from ℓ B))
    (t : transition A ℓ l (production.species E))
  : transition_from.mk (parL_species B t) ∈ enumerate_parallel_ts A B As Bs :=
  let h := @fintype.complete _ As (transition_from.mk t) in
  let g := finset.mem_map_of_mem (parL.embed A B) h in
  finset.mem_union_disjoint.mpr (or.inr (finset.mem_union_disjoint.mpr (or.inl g)))

private lemma enumate_parallel_compute_r_species
    {Γ ℓ} {A B : species ℍ ω Γ} {l : label ℍ Γ kind.species} {E}
    (As : fintype (transition_from ℓ A)) (Bs : fintype (transition_from ℓ B))
    (t : transition B ℓ l (production.species E))
  : transition_from.mk (parR_species A t) ∈ enumerate_parallel_ts A B As Bs :=
  let h := @fintype.complete _ Bs (transition_from.mk t) in
  let g := finset.mem_map_of_mem (parR.embed A B) h in
  finset.mem_union_disjoint.mpr (or.inr (finset.mem_union_disjoint.mpr (or.inr g)))

private lemma enumerate_parallel_complete {Γ} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
    (As : fintype (transition.transition_from ℓ A)) (Bs : fintype (transition.transition_from ℓ B))
  : ∀ x, x ∈ enumerate_parallel_ts A B As Bs
| ⟨ k, α, E, parL_species _ t ⟩ := enumate_parallel_compute_l  As Bs t
| ⟨ k, α, E, parL_concretion _ t ⟩ :=
  let h := @fintype.complete _ As (transition_from.mk t) in
  let g := finset.mem_map_of_mem (parL.embed A B) h in
  finset.mem_union_disjoint.mpr (or.inr (finset.mem_union_disjoint.mpr (or.inl g)))
| ⟨ k, α, E, parR_species _ t ⟩ := enumate_parallel_compute_r_species As Bs t
| ⟨ k, α, E, parR_concretion _ t ⟩ :=
  let h := @fintype.complete _ Bs (transition_from.mk t) in
  let g := finset.mem_map_of_mem (parR.embed A B) h in
  finset.mem_union_disjoint.mpr (or.inr (finset.mem_union_disjoint.mpr (or.inr g)))
| ⟨ k, α, E, com₁ eqFG eqα tf tg ⟩ := begin
  subst eqFG, subst eqα,
  let t : com₁.compatible ℓ A B
    := ⟨ ( transition_from.mk tf, transition_from.mk tg ), ⟨ rfl, rfl ⟩ ⟩,
  have h
    := finset.mem_subtype.mpr
      (finset.mem_product.mpr ⟨ @fintype.complete _ As t.val.1, @fintype.complete _ Bs t.val.2 ⟩),
  from finset.mem_union_disjoint.mpr (or.inl (finset.mem_map_of_mem (com₁.embed ℓ A B) h)),
end

/-- The set of all transitions from a parallel composition of species -/
def enumerate_parallel {Γ} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ}
  : fintype (transition.transition_from ℓ A)
  → fintype (transition.transition_from ℓ B)
  → fintype (transition.transition_from ℓ (A |ₛ B))
| As Bs := ⟨ enumerate_parallel_ts A B As Bs, enumerate_parallel_complete A B As Bs ⟩

private def com₂.wrap {Γ} {ℓ : lookup ℍ ω Γ}
    (M : affinity ℍ) {A B : species ℍ ω (context.extend M.arity Γ)}
  :
  ∀ (a b : name (context.extend M.arity Γ))
  , A [lookup.rename name.extend ℓ, τ⟨ a, b ⟩]⟶ (production.species B)
  → option (transition_from ℓ (ν(M) A))
| (name.zero a) (name.zero b) t :=
  if h : option.is_some (M.f a b) then some (transition_from.mk (com₂ M h t))
  else none
| (name.zero a) (name.extend b) t := none
| (name.extend a) (name.zero b) t := none
| (name.extend a) (name.extend b) t := none


/-- Show that the available transitions from a species is finite and thus
    enumerable.-/
constant enumerate :
  ∀ {Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ)
  , fintype (transition_from ℓ A)
/-
| Γ ℓ nil := enumerate_nil
| Γ ℓ (apply D as) := enumerate_apply ℓ D as
| Γ ℓ (A |ₛ B) := enumerate_parallel (enumerate ℓ A) (enumerate ℓ B)
| Γ ℓ (Σ# As) := enumerate_choices ℓ As
| Γ ℓ (ν(M) A) := {!!}
-/

noncomputable instance {Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ)
  : fintype (transition_from ℓ A)
  := enumerate ℓ A

end transition
end cpi

#lint-

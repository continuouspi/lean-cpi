import data.cpi.transition.basic

namespace cpi
namespace transition

variables {ℍ : Type} {ω : context}

/-- ξ_choice acts as an embedding. This is effectively ξ_choice.inj but
    lifted to transitions. -/
def ξ_choice.embed
    {Γ f} (ℓ : lookup ℍ ω Γ)
    (π : prefix_expr ℍ Γ f) (A : species ℍ ω (f.apply Γ)) (As : species.choices ℍ ω Γ)
  : transition_from ℓ (Σ# As) ↪ transition_from ℓ (Σ# (whole.cons π A As))
  := { to_fun := λ t, transition_from.mk (ξ_choice t.2.2.2),
       inj := λ ⟨ k, α, E, t ⟩ ⟨ k', α', E', t' ⟩ eq, by { cases eq, from rfl} }

/-- Temporary proof of equality of transitions. We'll show this one day. -/
noncomputable def transition_eq {ℍ} {ω} {Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ) :
  decidable_eq (transition_from ℓ A) := classical.dec_eq _

local attribute [instance] transition_eq

/-- Show that the available transitions from a choices species is finite and
    thus enumerable.-/
noncomputable def enumerate_choices {Γ} (ℓ : lookup ℍ ω Γ) :
  ∀ (As : species.choices ℍ ω Γ), fintype (transition_from ℓ (Σ# As))
| species.whole.empty :=
  { elems := finset.empty,
    complete := λ ⟨ k, α, E, t ⟩, by cases t }
| (species.whole.cons (a#(b; y)) A As) :=
  { elems :=
      insert (transition_from.mk (choice₁ a b y A As))
             (finset.map (ξ_choice.embed ℓ _ A As) ((enumerate_choices As).elems)),
    complete := λ x, begin
      rcases x with ⟨ k, α, E, t ⟩,
      cases t,
      case ξ_choice {
        have : transition_from.mk t_a ∈ (enumerate_choices As).elems
          := @fintype.complete _ (enumerate_choices As) _,
        have this := finset.mem_map_of_mem (ξ_choice.embed ℓ _ A As) this,
        from finset.mem_insert_of_mem this,
      },
      case choice₁ { from finset.mem_insert_self _ _ },
    end }
| (species.whole.cons (τ@k) A As) :=
  { elems :=
      insert (transition_from.mk (choice₂ k A As))
             (finset.map (ξ_choice.embed ℓ _ A As) ((enumerate_choices As).elems)),
    complete := λ x, begin
      rcases x with ⟨ k, α, E, t ⟩,
      cases t,
      case ξ_choice {
        have : transition_from.mk t_a ∈ (enumerate_choices As).elems
          := @fintype.complete _ (enumerate_choices As) _,
        have this := finset.mem_map_of_mem (ξ_choice.embed ℓ _ A As) this,
        from finset.mem_insert_of_mem this,
      },
      case choice₂ { from finset.mem_insert_self _ _ },
    end }

/-- defn lifted to transition_from.

    While this is probably an embedding, getting the proofs to go through
    without injectivity on `(name.mk_apply as)` is /annoying/. -/
def defn.from
    {Γ n} (ℓ : lookup ℍ ω Γ)
    (D : reference n ω) (as : vector (name Γ) n)
  : transition_from (lookup.rename name.extend ℓ) (Σ# (ℓ n D))
  → transition_from ℓ (apply D as)
| t := transition_from.mk (defn ℓ D as t.2.2.2)

private def com₂.wrap {Γ} {ℓ : lookup ℍ ω Γ}
    (M : affinity ℍ) {A B : species ℍ ω (context.extend M.arity Γ)}
  :
  ∀ (a b : name (context.extend M.arity Γ))
  , A [lookup.rename name.extend ℓ, τ⟨ a, b ⟩]⟶ B
  → option (transition_from ℓ (ν(M) A))
| (name.zero a) (name.zero b) t :=
  if h : option.is_some (M.f a b) then some (transition_from.mk (com₂ M h t))
  else none
| (name.zero a) (name.extend b) t := none
| (name.extend a) (name.zero b) t := none
| (name.extend a) (name.extend b) t := none

/- com₂ lifted to transition_from. -/
/-
def com₂.from {Γ ℓ} (M : affinity ℍ) :
  ∀ {A : species ℍ ω (context.extend M.arity Γ)}
  , transition_from (lookup.rename name.extend ℓ) A
  → option (transition_from ℓ (ν(M) A))
| A ⟨ _, τ⟨ p ⟩, production.species E, t ⟩ := begin
  induction p using quot.hrec_on,
  { rcases p with ⟨ a, b ⟩, from com₂.wrap M a b t },
  {
    rcases p_a with ⟨ p₁, p₂ ⟩, rcases p_b with ⟨ q₁, q₂ ⟩, simp only [],
    rcases p with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
    from heq_of_eq rfl,

    have : (upair.mk p₁ p₂) = (upair.mk p₂ p₁) := quot.sound (or.inr ⟨ rfl, rfl ⟩),
    refine function.hfunext (by rw this) _,
    { assume t t' teq, simp only [heq_iff_eq],
      cases p₁,
      case name.extend { cases p₂; unfold com₂.wrap },
      case name.zero {
        cases p₂; unfold com₂.wrap,
        by_cases (option.is_some (M.f p₁_a p₂_a) = tt),
        {
          have h' : (option.is_some (M.f p₂_a p₁_a) = tt), { rw M.symm, from h },
          simp only [dif_pos h, dif_pos h'],

          show transition_from.mk (com₂ M h t) = transition_from.mk (com₂ M h' t'),
          sorry,
        },
        {
          have h' : ¬(option.is_some (M.f p₂_a p₁_a) = tt), { rw M.symm, from h },
          simp only [dif_neg h, dif_neg h'],
        }
      }
    }
  }
end
| A ⟨ _, τ@'_, production.species E, t ⟩ := none
| A ⟨ _, #_, production.concretion E, t ⟩ := none
-/

/-- Show that the available transitions from a species is finite and thus
    enumerable.-/
noncomputable constant enumerate :
  ∀ {Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ)
  , fintype (transition_from ℓ A)
/-
| Γ ℓ nil :=
  { elems := finset.empty,
    complete := λ ⟨ k, α, E, t ⟩, by cases t }
| Γ ℓ (apply D as) :=
  { elems := finset.image (defn.from ℓ D as)
      (enumerate_choices (lookup.rename name.extend ℓ) (ℓ _ D)).elems,
    complete := λ x, begin
      rcases x with ⟨ k, α, E, t ⟩, cases t with α E t,
      have : transition_from.mk t_a ∈ (enumerate_choices _ (ℓ _ D)).elems
          := @fintype.complete _ (enumerate_choices _ (ℓ _ D)) _,
      from finset.mem_image_of_mem (defn.from ℓ D as) this,
    end }
| Γ ℓ (A |ₛ B) := {!!}
| Γ ℓ (Σ# As) := enumerate_choices ℓ As
| Γ ℓ (ν(M) A) := {!!}
-/

noncomputable instance {Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ)
  : fintype (transition_from ℓ A)
  := enumerate ℓ A

end transition
end cpi

#lint-

import data.cpi.transition.basic

namespace cpi
namespace transition

variables {ℍ : Type} {ω : context}

private def ξ_choice.embed
    {Γ f} (ℓ : lookup ℍ ω Γ)
    (π : prefix_expr ℍ Γ f) (A : species ℍ ω (f.apply Γ)) (As : species.choices ℍ ω Γ)
  : transition_from ℓ (Σ# As) ↪ transition_from ℓ (Σ# (whole.cons π A As))
  := { to_fun := λ t, ⟨ _, _, _, ξ_choice t.2.2.2 ⟩,
       inj := λ ⟨ k, α, E, t ⟩ ⟨ k', α', E', t' ⟩ eq, begin
        simp only [] at eq, unfold_projs at eq,
        cases eq, from rfl,
       end }

local attribute [instance] classical.dec_eq

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

/-- Show that the available transitions from a species is finite and thus
    enumerable.-/
noncomputable constant enumerate :
  ∀ {Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ)
  , fintype (transition_from ℓ A)
/-
| Γ ℓ nil :=
  { elems := finset.empty,
    complete := λ ⟨ k, α, E, t ⟩, by cases t }
| Γ ℓ (apply D as) := {!!}
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

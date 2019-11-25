import data.cpi.transition.basic

namespace cpi
namespace transition

variables {ℍ : Type} {ω : context}

private lemma ξ_choice.embed
    {Γ f} (ℓ : lookup ℍ ω Γ)
    (π : prefix_expr ℍ Γ f) (A : species ℍ ω (f Γ)) (As : species.choices ℍ ω Γ)
  : transition_from ℓ (Σ# As) ↪ transition_from ℓ (Σ# (whole.cons π A As))
  := { to_fun := λ t, ⟨ _, _, _, ξ_choice t.2.2.2 ⟩,
       inj := λ ⟨ k, α, E, t ⟩ ⟨ k', α', E', t' ⟩ eq, begin
        simp only [] at eq, unfold_projs at eq,
        cases eq, from rfl,
       end }

/-- Show that the available transitions from a choices species is finite and
    thus enumerable.-/
constant enumerate_choices :
  ∀ {Γ} (ℓ : lookup ℍ ω Γ) (As : species.choices ℍ ω Γ), fintype (transition_from ℓ (Σ# As))
/-
| Γ ℓ species.whole.empty :=
  { elems := finset.empty,
    complete := λ ⟨ k, α, E, t ⟩, by cases t }
| Γ ℓ (species.whole.cons (a#(b; y)) A As) :=
  { elems :=
      insert (⟨ _, _, _, choice₁ a b y A As ⟩ : transition_from ℓ _)
             (finset.map (ξ_choice.embed ℓ _ A As) ((enumerate.choices ℓ As).elems)),
    complete := λ x, begin
      rcases x with ⟨ k, α, E, t ⟩,
      -- cases k,
      -- cases α,
      cases t,
    end }
-/

/-- Show that the available transitions from a species is finite and thus
    enumerable.-/
constant enumerate :
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

#lint
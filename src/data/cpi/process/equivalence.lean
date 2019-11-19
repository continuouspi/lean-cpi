import data.cpi.species data.cpi.process.basic

namespace cpi
namespace process

variables {ℍ : Type} {ω : context} [has_add ℍ]

/-- Structural congruence of processes. -/
inductive equiv {Γ} : process ℍ ω Γ → process ℍ ω Γ → Prop
| refl  {A : process ℍ ω Γ} : equiv A A
| trans {A B C : process ℍ ω Γ} : equiv A B → equiv B C → equiv A C
| symm  {A B : process ℍ ω Γ} : equiv A B → equiv B A

-- Projection
| ξ_species   {c : ℍ} {A B : species ℍ ω Γ} : A ≈ B → equiv (c ◯ A) (c ◯ B)
| ξ_parallel₁ {P P' Q : process ℍ ω Γ} : equiv P P' → equiv (P |ₚ Q) (P' |ₚ Q)
| ξ_parallel₂ {P Q Q' : process ℍ ω Γ} : equiv Q Q' → equiv (P |ₚ Q) (P |ₚ Q')

-- Monoidic properties
| parallel_nil   {P : process ℍ ω Γ} {c : ℍ} : equiv (P |ₚ c ◯ species.nil) P
| parallel_symm  {P Q : process ℍ ω Γ} : equiv (P |ₚ Q) (Q |ₚ P)
| parallel_assoc {P Q R : process ℍ ω Γ} : equiv ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

-- Join identical species together.
| join  {A : species ℍ ω Γ} {c d : ℍ} : equiv (c ◯ A |ₚ d ◯ A) ((c + d) ◯ A)

instance {Γ} : is_equiv (process ℍ ω Γ) equiv :=
  { refl := @equiv.refl _ _ _ Γ, symm := @equiv.symm _ _ _ Γ, trans := @equiv.trans _ _ _ Γ }
instance {Γ} : is_refl (process ℍ ω Γ) equiv := ⟨ λ _, equiv.refl ⟩
instance {Γ} : setoid (process ℍ ω Γ) :=
  ⟨ equiv, ⟨ @equiv.refl _ _ _ Γ, @equiv.symm _ _ _ Γ, @equiv.trans _ _ _ Γ ⟩ ⟩
instance setoid.is_equiv {Γ} : is_equiv (process ℍ ω Γ) has_equiv.equiv :=
  process.is_equiv

end process
end cpi

#lint

import data.cpi.species data.cpi.process.basic

namespace cpi
namespace process

variable {ω : context}

inductive equiv {Γ} : process ω Γ → process ω Γ → Prop
| refl  {A : process ω Γ} : equiv A A
| trans {A B C : process ω Γ} : equiv A B → equiv B C → equiv A C
| symm  {A B : process ω Γ} : equiv A B → equiv B A

-- Projection
| ξ_species   {c : ℝ≥0} {A B : species ω Γ} : A ≈ B → equiv (c • A) (c • B)
| ξ_parallel₁ {P P' Q : process ω Γ} : equiv P P' → equiv (P |ₚ Q) (P' |ₚ Q)
| ξ_parallel₂ {P Q Q' : process ω Γ} : equiv Q Q' → equiv (P |ₚ Q) (P |ₚ Q')

-- Monoidic properties
| parallel_nil   {P : process ω Γ} {c : ℝ≥0} : equiv (P |ₚ c • species.nil) P
| parallel_sym   {P Q : process ω Γ} : equiv (P |ₚ Q) (Q |ₚ P)
| parallel_assoc {P Q R : process ω Γ} : equiv ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

-- Join identical species together.
| join  {A : species ω Γ} {c d : ℝ≥0} : equiv (c • A |ₚ d • A) ((c + d) • A)

instance {Γ} : is_equiv (process ω Γ) equiv :=
  { refl := @equiv.refl _ Γ, symm := @equiv.symm _ Γ, trans := @equiv.trans _ Γ }
instance {Γ} : is_refl (process ω Γ) equiv := ⟨ λ _, equiv.refl ⟩
instance {Γ} : setoid (process ω Γ) :=
  ⟨ equiv, ⟨ @equiv.refl _ Γ, @equiv.symm _ Γ, @equiv.trans _ Γ ⟩ ⟩
instance setoid.is_equiv {Γ} : is_equiv (process ω Γ) has_equiv.equiv :=
  process.is_equiv

end process
end cpi

#lint

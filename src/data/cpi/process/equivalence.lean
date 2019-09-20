import data.cpi.species
import data.cpi.process.basic

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi
namespace process

inductive equiv {Γ : context} : process Γ → process Γ → Prop
| refl  {A : process Γ} : equiv A A
| trans {A B C : process Γ} : equiv A B → equiv B C → equiv A C
| symm  {A B : process Γ} : equiv A B → equiv B A

-- Projection
| ξ_species   {c : ℝ≥0} {A B : species Γ} : A ≈ B → equiv (c • A) (c • B)
| ξ_parallel₁ {P P' Q : process Γ} : equiv P P' → equiv (P |ₚ Q) (P' |ₚ Q)
| ξ_parallel₂ {P Q Q' : process Γ} : equiv Q Q' → equiv (P |ₚ Q) (P |ₚ Q')

-- Monoidic properties
| parallel_nil   {P : process Γ} {c : ℝ≥0} : equiv (P |ₚ c • species.nil) P
| parallel_sym   {P Q : process Γ} : equiv (P |ₚ Q) (Q |ₚ P)
| parallel_assoc {P Q R : process Γ} : equiv ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

-- Join identical species together.
| join  {A : species Γ} {c d : ℝ≥0} : equiv (c • A |ₚ d • A) ((c + d) • A)

instance {Γ} : is_equiv (process Γ) equiv :=
  { refl := @equiv.refl Γ, symm := @equiv.symm Γ, trans := @equiv.trans Γ }
instance {Γ} : is_refl (process Γ) equiv := ⟨ λ _, equiv.refl ⟩
instance {Γ} : setoid (process Γ) :=
  ⟨ equiv, ⟨ @equiv.refl Γ, @equiv.symm Γ, @equiv.trans Γ ⟩ ⟩
instance setoid.is_equiv {Γ} : is_equiv (process Γ) has_equiv.equiv :=
  process.is_equiv

end process
end cpi

#sanity_check

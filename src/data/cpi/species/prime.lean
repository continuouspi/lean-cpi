import data.cpi.species.equivalence

set_option profiler true
set_option profiler.threshold 0.5

namespace cpi
namespace species

variable {ω : context}

/-- A species is prime if it is non-nil, and for any decomposition into two
    parallel species, one of those must be nil.  -/
def prime {Γ} (A : species ω Γ) : Prop
  := ¬ A ≈ nil ∧ ∀ (B C : species ω Γ), A ≈ (B |ₛ C) → B ≈ nil ∨ C ≈ nil

lemma prime.equivalent_imp {Γ} {A B : species ω Γ} : A ≈ B → prime A → prime B
| ab ⟨ neq, prime ⟩ := ⟨ λ nil, neq (trans ab nil), λ A B eq, prime A B (trans ab eq) ⟩

/-- Primality commutes with structrural congruence. -/
lemma prime.equivalent {Γ} {A B : species ω Γ} : A ≈ B → prime A = prime B
| eq := propext ⟨ prime.equivalent_imp eq, prime.equivalent_imp (symm eq) ⟩

/-- The set of all species which are prime. -/
def prime_species : context → context → Type
| ω Γ := { A : species ω Γ // prime A }

end species
end cpi

#lint

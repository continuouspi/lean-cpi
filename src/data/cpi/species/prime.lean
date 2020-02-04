import data.cpi.species.congruence

namespace cpi
namespace species

variables {ℍ : Type} {ω : context}

/-- A species is prime if it is non-nil, and for any decomposition into two
    parallel species, one of those must be nil.  -/
def prime {Γ} (A : species ℍ ω Γ) : Prop
  := ¬ A ≈ nil ∧ ∀ (B C : species ℍ ω Γ), A ≈ (B |ₛ C) → B ≈ nil ∨ C ≈ nil

lemma prime.equivalent_imp {Γ} {A B : species ℍ ω Γ} : A ≈ B → prime A → prime B
| ab ⟨ neq, prime ⟩ := ⟨ λ nil, neq (trans ab nil), λ A B eq, prime A B (trans ab eq) ⟩

/-- Primality commutes with structrural congruence. -/
lemma prime.equivalent {Γ} {A B : species ℍ ω Γ} : A ≈ B → prime A = prime B
| eq := propext ⟨ prime.equivalent_imp eq, prime.equivalent_imp (symm eq) ⟩

/-- The set of all species which are prime. -/
def prime_species : Type → context → context → Type
| ℍ ω Γ := { A : species ℍ ω Γ // prime A }

instance prime_species.setoid {ω Γ} : setoid (prime_species ℍ ω Γ)
  := ⟨ λ A B, A.val ≈ B.val, ⟨ λ _, equiv.rfl, λ _ _, equiv.symm, λ _ _ _, equiv.trans ⟩ ⟩

/-- A quotient of all structurally congruent species which are prime. -/
def prime_species' (ℍ : Type) (ω Γ : context) := quotient (@prime_species.setoid ℍ ω Γ)

/-- Unwrap a quotient of prime species, yielding a quotient of species. -/
def prime_species.unwrap {ω Γ} : prime_species' ℍ ω Γ → species' ℍ ω Γ
| A := quot.lift_on A (λ B, ⟦ B.val ⟧) (λ _ _ eq, quot.sound eq)

lemma prime_species.unwrap.inj {ω Γ} :
  ∀ (A B : prime_species' ℍ ω Γ), prime_species.unwrap A = prime_species.unwrap B
  → A = B
| A B eq := begin
  rcases quotient.exists_rep A with ⟨ A, eq ⟩, subst eq,
  rcases quotient.exists_rep B with ⟨ B, eq ⟩, subst eq,
  from quot.sound (quotient.exact eq),
end

end species
end cpi

#lint-

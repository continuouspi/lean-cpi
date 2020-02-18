import data.cpi.species.basic

-- Dubious instances to force setoids to be equivalent.
instance {α : Type*} [r : setoid α] : is_refl α has_equiv.equiv
  := { refl := λ a, r.iseqv.1 a }
instance {α : Type*} [r : setoid α] : is_trans α has_equiv.equiv
  := { trans := λ a b c ab bc, r.iseqv.2.2 ab bc }
instance {α : Type*} [r : setoid α] : is_symm α has_equiv.equiv
  := { symm := λ a b ab, r.iseqv.2.1 ab }

namespace cpi
namespace species

variables {ℍ : Type} {ω Γ : context} [setoid (species ℍ ω Γ)]

/-- A species is prime if it is non-nil, and for any decomposition into two
    parallel species, one of those must be nil.  -/
def prime (A : species ℍ ω Γ) : Prop
  := ¬ A ≈ nil ∧ ∀ (B C : species ℍ ω Γ), A ≈ (B |ₛ C) → B ≈ nil ∨ C ≈ nil

lemma prime.equivalent_imp {A B : species ℍ ω Γ} : A ≈ B → prime A → prime B
| ab ⟨ neq, prime ⟩ := ⟨ λ nil, neq (trans ab nil), λ A B eq, prime A B (trans ab eq) ⟩

/-- Primality commutes with structrural congruence. -/
lemma prime.equivalent {A B : species ℍ ω Γ} : A ≈ B → prime A = prime B
| eq := propext ⟨ prime.equivalent_imp eq, prime.equivalent_imp (symm eq) ⟩

/-- The set of all species which are prime. -/
def prime_species (ℍ : Type) (ω Γ : context) [setoid (species ℍ ω Γ)] :Type
  := { A : species ℍ ω Γ // prime A }

instance prime_species.setoid: setoid (prime_species ℍ ω Γ) :=
  { r := λ A B, A.val ≈ B.val,
    iseqv := ⟨ λ a, by from refl a.val,
              λ _ _ ab, by from symm ab,
              λ _ _ _ ab bc, by from trans ab bc ⟩ }

/-- A quotient of all structurally congruent species which are prime. -/
def prime_species' (ℍ : Type) (ω Γ : context) [r : setoid (species ℍ ω Γ)] :=
  quotient (@prime_species.setoid ℍ ω Γ r)

/-- Unwrap a quotient of prime species, yielding a quotient of species. -/
def prime_species.unwrap : prime_species' ℍ ω Γ → species' ℍ ω Γ
| A := quot.lift_on A (λ B, ⟦ B.val ⟧) (λ _ _ eq, quot.sound eq)

lemma prime_species.unwrap.inj :
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

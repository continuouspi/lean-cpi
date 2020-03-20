import data.cpi.semantics.relation

namespace cpi
namespace normalise

open_locale normalise

variables {ℍ : Type} {ω : context}

/-- "Equivalence" of concretions, just defined as exact equality for now. -/
def concretion_setoid {b y Γ} : setoid (concretion ℍ ω b y Γ) := ⟨ eq, eq_equivalence ⟩

localized "attribute [instance] cpi.normalise.concretion_setoid" in normalise

instance concretion.has_repr [has_repr ℍ] {b y Γ} : has_repr (concretion' ℍ ω b y Γ) :=
  ⟨ λ x, quot.lift_on x repr (λ x y eql, by { cases eql, from rfl }) ⟩

/-- `cpi.cpi_equiv` for n-equivalence -/
def cpi_equiv (ℍ : Type) (ω : context) [decidable_eq ℍ] : cpi_equiv ℍ ω :=
  { species_equiv := by apply_instance,
    concretion_equiv := by apply_instance,
    decide_species := by apply_instance,
    decide_concretion := by apply_instance,
    prime_decompose := λ Γ A, species.normalise.prime_decompose A,
    prime_decompose_equiv := λ Γ A B equ, by rw species.normalise.prime_decompose.equiv equ,
    prime_decompose_nil := λ Γ, by { rw species.normalise.prime_decompose.nil, from rfl },
    prime_decompose_parallel := λ Γ A B, by { rw species.normalise.prime_decompose.parallel, from rfl },
    prime_decompose_prime := λ Γ A, by rw species.normalise.prime_decompose.prime,
    pseudo_apply := λ Γ b y F G, quotient.lift_on₂ F G
      (λ F G, ⟦ concretion.pseudo_apply F G ⟧)
      (λ F G F' G' eqF eqG, by { cases eqF, cases eqG, from rfl }) }

localized "attribute [instance] cpi.normalise.cpi_equiv" in normalise

end normalise
end cpi

#lint-

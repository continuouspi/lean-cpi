import data.cpi.semantics.space

namespace cpi

open_locale normalise

def cpi_equiv.normalise (ℍ : Type) (ω : context) [decidable_eq ℍ] : cpi_equiv ℍ ω :=
  { species_equiv := by apply_instance,
    concretion_equiv := λ Γ b y, concretion.equiv.setoid,
    decide_species := by apply_instance,
    decide_concretion := sorry,
    prime_decompose := λ Γ, species.normalise.prime_decompose',
    prime_decompose_nil := λ Γ, species.normalise.prime_decompose'.nil,
    prime_decompose_parallel := λ Γ, species.normalise.prime_decompose'.parallel,
    prime_decompose_prime := λ Γ, species.normalise.prime_decompose'.prime,
    pseudo_apply := begin
      sorry,
    end }

localized "attribute [instance] cpi_equiv.normalise" in normalise

end cpi

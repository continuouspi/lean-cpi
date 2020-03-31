import data.cpi.semantics.relation

namespace cpi

namespace congruence

variables {ℍ : Type} {ω : context}

open_locale congruence
open species.equiv

axiom prime_decompose_parallel {Γ} (A B : species ℍ ω Γ) : prime_decompose (A |ₛ B) = prime_decompose A + prime_decompose B
axiom prime_decompose_equiv {Γ} {A B : species ℍ ω Γ}
  : A ≈ B
  → multiset.map quotient.mk (prime_decompose A)
  = multiset.map quotient.mk (prime_decompose B)

/-- A relation for semantics evaluation using structrual congruence. This is non-computable due to using classical logic
    in order to decide A≈B, and to compute the prime normalisation. -/
noncomputable def cpi_equiv_prop (ℍ : Type) (ω : context) : cpi_equiv_prop ℍ ω :=
  { species_equiv := by apply_instance,
    concretion_equiv := by apply_instance,
    decide_species := λ Γ, classical.dec_rel _,
    decide_concretion := λ Γ b y, classical.dec_rel _,
    prime_decompose := λ Γ, prime_decompose,
    prime_decompose_equiv := λ Γ A B, prime_decompose_equiv,
    prime_decompose_nil := λ Γ, prime_decompose_nil,
    prime_decompose_parallel := λ Γ, prime_decompose_parallel,
    prime_decompose_prime := λ Γ, prime_decompose_prime,
    pseudo_apply := λ Γ b y, concretion.pseudo_apply.quotient,
    transition_iso := λ Γ ℓ A B ⟨ eq ⟩, ⟨ λ k α,
      ⟨ transition.equivalent_of.is_equiv eq, transition.equivalent_of.map_equiv eq ⟩ ⟩,
    pseudo_apply_symm := λ Γ b y, concretion.pseudo_apply.quotient.symm }

localized "attribute [instance] cpi.congruence.cpi_equiv_prop" in congruence

end congruence

end cpi

#lint-
